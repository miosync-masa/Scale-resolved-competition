# =============================================================================
#  diagnostics.py — Global and shell-resolved enstrophy budget diagnostics
#
#  Global:  Omega(t), P(t), D(t), R(t) = P/D
#  Shell:   P(k,t), D(k,t), R(k,t) = P(k)/D(k)
#
#  Parseval normalization:
#    JAX/NumPy fftn is unnormalized: X[k] = sum_n x[n] exp(-2pi i k.n/N)
#    Parseval: sum_n x[n]*conj(y[n]) = (1/N^3) sum_k X[k]*conj(Y[k])
#    Therefore: mean(x*y) = (1/N^6) sum_k X[k]*conj(Y[k])
#    All shell sums use /(N^3 * N^3) to match global mean()-based quantities.
# =============================================================================

import jax.numpy as jnp
from jax import jit
from jax.numpy.fft import fftn, ifftn
import numpy as np
from functools import partial


def compute_global_metrics(solver, u_hat, v_hat, w_hat):
    """
    Compute global enstrophy budget: Omega, P, D, R, omega_max.

    Omega = (1/2) <|omega|^2>
    P     = <omega . S . omega>
    D     = nu <|nabla omega|^2>
    R     = P / D
    """
    KX, KY, KZ = solver.KX, solver.KY, solver.KZ
    nu = solver.nu

    # vorticity in physical space
    omega_x = ifftn(1j * KY * w_hat - 1j * KZ * v_hat).real
    omega_y = ifftn(1j * KZ * u_hat - 1j * KX * w_hat).real
    omega_z = ifftn(1j * KX * v_hat - 1j * KY * u_hat).real

    omega_sq = omega_x**2 + omega_y**2 + omega_z**2
    Omega = 0.5 * jnp.mean(omega_sq)
    omega_max = jnp.max(jnp.sqrt(omega_sq))

    # strain tensor
    dudx = ifftn(1j * KX * u_hat).real
    dudy = ifftn(1j * KY * u_hat).real
    dudz = ifftn(1j * KZ * u_hat).real
    dvdx = ifftn(1j * KX * v_hat).real
    dvdy = ifftn(1j * KY * v_hat).real
    dvdz = ifftn(1j * KZ * v_hat).real
    dwdx = ifftn(1j * KX * w_hat).real
    dwdy = ifftn(1j * KY * w_hat).real
    dwdz = ifftn(1j * KZ * w_hat).real

    S_xx = dudx
    S_yy = dvdy
    S_zz = -(S_xx + S_yy)  # incompressibility
    S_xy = 0.5 * (dudy + dvdx)
    S_xz = 0.5 * (dudz + dwdx)
    S_yz = 0.5 * (dvdz + dwdy)

    # P = <omega . S . omega>
    omega_S_omega = (
        omega_x * (S_xx * omega_x + S_xy * omega_y + S_xz * omega_z) +
        omega_y * (S_xy * omega_x + S_yy * omega_y + S_yz * omega_z) +
        omega_z * (S_xz * omega_x + S_yz * omega_y + S_zz * omega_z)
    )
    P = jnp.mean(omega_S_omega)

    # D = nu <|nabla omega|^2>
    omega_x_hat = fftn(omega_x)
    omega_y_hat = fftn(omega_y)
    omega_z_hat = fftn(omega_z)

    grad_omega_sq = jnp.zeros_like(omega_x)
    for om_hat in [omega_x_hat, omega_y_hat, omega_z_hat]:
        for K_comp in [KX, KY, KZ]:
            grad_omega_sq += ifftn(1j * K_comp * om_hat).real ** 2

    D = nu * jnp.mean(grad_omega_sq)
    R = P / (D + 1e-15)

    return Omega, P, D, R, omega_max


def compute_shell_metrics(solver, u_hat, v_hat, w_hat):
    """
    Shell-resolved enstrophy budget: P(k), D(k), R(k).

    Uses spherical shell projectors:
      K_k = { kappa in Z^3 : k - 0.5 < |kappa| <= k + 0.5 }

    P(k) = <omega_k . P_k[ (omega . nabla) v ]>
    D(k) = nu * sum_{kappa in K_k} |kappa|^2 |omega_hat(kappa)|^2 / N^6

    Normalization: /(N^3 * N^3) ensures sum_k P(k) = P_global
    and sum_k D(k) = D_global (Parseval consistency).

    R(k) = P(k) / D(k)  where D(k) is significant;
    R(k) = NaN where shell enstrophy is negligible.
    """
    KX, KY, KZ = solver.KX, solver.KY, solver.KZ
    K_mag = solver.K_mag
    nu = solver.nu
    k_shells = solver.k_shells
    n_shells = len(k_shells)

    # vorticity in Fourier space
    omega_x_hat = 1j * KY * w_hat - 1j * KZ * v_hat
    omega_y_hat = 1j * KZ * u_hat - 1j * KX * w_hat
    omega_z_hat = 1j * KX * v_hat - 1j * KY * u_hat

    # stretching term (omega . nabla) v in physical space
    omega_x = ifftn(omega_x_hat).real
    omega_y = ifftn(omega_y_hat).real
    omega_z = ifftn(omega_z_hat).real

    dudx = ifftn(1j * KX * u_hat).real
    dudy = ifftn(1j * KY * u_hat).real
    dudz = ifftn(1j * KZ * u_hat).real
    dvdx = ifftn(1j * KX * v_hat).real
    dvdy = ifftn(1j * KY * v_hat).real
    dvdz = ifftn(1j * KZ * v_hat).real
    dwdx = ifftn(1j * KX * w_hat).real
    dwdy = ifftn(1j * KY * w_hat).real
    dwdz = ifftn(1j * KZ * w_hat).real

    # (omega . nabla) v  components
    stretch_x = omega_x * dudx + omega_y * dudy + omega_z * dudz
    stretch_y = omega_x * dvdx + omega_y * dvdy + omega_z * dvdz
    stretch_z = omega_x * dwdx + omega_y * dwdy + omega_z * dwdz

    stretch_x_hat = fftn(stretch_x)
    stretch_y_hat = fftn(stretch_y)
    stretch_z_hat = fftn(stretch_z)

    # shell-resolved computation (numpy for binning)
    K_mag_np = np.array(K_mag)
    shell_idx = np.round(K_mag_np).astype(int)

    omega_x_hat_np = np.array(omega_x_hat)
    omega_y_hat_np = np.array(omega_y_hat)
    omega_z_hat_np = np.array(omega_z_hat)
    stretch_x_hat_np = np.array(stretch_x_hat)
    stretch_y_hat_np = np.array(stretch_y_hat)
    stretch_z_hat_np = np.array(stretch_z_hat)
    K2_np = np.array(solver.K2)
    N3 = solver.N ** 3
    N6 = N3 * N3  # Parseval normalization factor

    Pk = np.zeros(n_shells)
    Dk = np.zeros(n_shells)

    for k_idx in range(n_shells):
        k_val = int(k_shells[k_idx])
        mask = (shell_idx == k_val)
        if not np.any(mask):
            continue

        # P(k) = Re[ sum_{kappa in shell} conj(omega_hat_k) . stretch_hat_k ] / N^6
        Pk[k_idx] = np.real(
            np.sum(
                np.conj(omega_x_hat_np[mask]) * stretch_x_hat_np[mask] +
                np.conj(omega_y_hat_np[mask]) * stretch_y_hat_np[mask] +
                np.conj(omega_z_hat_np[mask]) * stretch_z_hat_np[mask]
            )
        ) / N6

        # D(k) = nu * sum_{kappa in shell} |kappa|^2 |omega_hat(kappa)|^2 / N^6
        omega_sq_shell = (
            np.abs(omega_x_hat_np[mask])**2 +
            np.abs(omega_y_hat_np[mask])**2 +
            np.abs(omega_z_hat_np[mask])**2
        )
        Dk[k_idx] = nu * np.sum(K2_np[mask] * omega_sq_shell) / N6

    # R(k) only meaningful where shell has significant dissipation;
    # NaN marks shells with negligible enstrophy content
    Rk = np.where(Dk > 1e-30, Pk / Dk, np.nan)

    return Pk, Dk, Rk


def compute_energy_spectrum(solver, u_hat, v_hat, w_hat):
    """
    Compute shell-averaged energy spectrum E(k).

    E(k) = (1/2) sum_{kappa in K_k} |v_hat(kappa)|^2 / N^6

    Normalization: /(N^3 * N^3) ensures sum_k E(k) = E_global.
    """
    K_mag_np = np.array(solver.K_mag)
    shell_idx = np.round(K_mag_np).astype(int)
    N3 = solver.N ** 3
    N6 = N3 * N3

    u_hat_np = np.array(u_hat)
    v_hat_np = np.array(v_hat)
    w_hat_np = np.array(w_hat)

    n_shells = len(solver.k_shells)
    Ek = np.zeros(n_shells)

    for k_idx in range(n_shells):
        k_val = int(solver.k_shells[k_idx])
        mask = (shell_idx == k_val)
        if not np.any(mask):
            continue
        Ek[k_idx] = 0.5 * np.sum(
            np.abs(u_hat_np[mask])**2 +
            np.abs(v_hat_np[mask])**2 +
            np.abs(w_hat_np[mask])**2
        ) / N6

    return Ek


def compute_enstrophy_spectrum(solver, u_hat, v_hat, w_hat):
    """
    Compute shell-averaged enstrophy spectrum Omega(k).

    Omega(k) = (1/2) sum_{kappa in K_k} |omega_hat(kappa)|^2 / N^6

    This is equivalent to k^2 * E(k) up to shell-averaging effects.
    Useful for verifying spectral decay at high wavenumbers (Referee 3).
    """
    KX, KY, KZ = solver.KX, solver.KY, solver.KZ
    K_mag_np = np.array(solver.K_mag)
    shell_idx = np.round(K_mag_np).astype(int)
    N3 = solver.N ** 3
    N6 = N3 * N3

    omega_x_hat_np = np.array(1j * KY * w_hat - 1j * KZ * v_hat)
    omega_y_hat_np = np.array(1j * KZ * u_hat - 1j * KX * w_hat)
    omega_z_hat_np = np.array(1j * KX * v_hat - 1j * KY * u_hat)

    n_shells = len(solver.k_shells)
    Omega_k = np.zeros(n_shells)

    for k_idx in range(n_shells):
        k_val = int(solver.k_shells[k_idx])
        mask = (shell_idx == k_val)
        if not np.any(mask):
            continue
        Omega_k[k_idx] = 0.5 * np.sum(
            np.abs(omega_x_hat_np[mask])**2 +
            np.abs(omega_y_hat_np[mask])**2 +
            np.abs(omega_z_hat_np[mask])**2
        ) / N6

    return Omega_k


def verify_shell_sum(solver, u_hat, v_hat, w_hat):
    """
    Verify Parseval consistency: sum_k P(k) = P_global,
    sum_k D(k) = D_global, sum_k E(k) = E_global.

    This test ensures that the shell decomposition is exhaustive
    and that the normalization is consistent between global
    (physical-space mean) and shell (Fourier-space sum) computations.

    Raises AssertionError if any relative discrepancy exceeds 1e-6.
    """
    Omega, P_global, D_global, _, _ = compute_global_metrics(solver, u_hat, v_hat, w_hat)
    Pk, Dk, _ = compute_shell_metrics(solver, u_hat, v_hat, w_hat)
    Ek = compute_energy_spectrum(solver, u_hat, v_hat, w_hat)

    # --- P check ---
    P_sum = np.sum(Pk)
    P_err = abs(P_sum - float(P_global)) / (abs(float(P_global)) + 1e-30)

    # --- D check ---
    D_sum = np.sum(Dk)
    D_err = abs(D_sum - float(D_global)) / (abs(float(D_global)) + 1e-30)

    # --- E check ---
    E_sum = np.sum(Ek)
    E_global = 0.5 * float(jnp.mean(
        jnp.abs(ifftn(u_hat))**2 +
        jnp.abs(ifftn(v_hat))**2 +
        jnp.abs(ifftn(w_hat))**2
    ))
    E_err = abs(E_sum - E_global) / (abs(E_global) + 1e-30)

    # --- Omega check ---
    Omega_k = compute_enstrophy_spectrum(solver, u_hat, v_hat, w_hat)
    Omega_sum = np.sum(Omega_k)
    Omega_err = abs(Omega_sum - float(Omega)) / (abs(float(Omega)) + 1e-30)

    print("=" * 60)
    print("  Shell-sum Parseval consistency check")
    print("=" * 60)
    print(f"  P: global={float(P_global):.10e}, sum={P_sum:.10e}, rel_err={P_err:.2e}")
    print(f"  D: global={float(D_global):.10e}, sum={D_sum:.10e}, rel_err={D_err:.2e}")
    print(f"  E: global={E_global:.10e},         sum={E_sum:.10e}, rel_err={E_err:.2e}")
    print(f"  Ω: global={float(Omega):.10e}, sum={Omega_sum:.10e}, rel_err={Omega_err:.2e}")
    print("=" * 60)

    assert P_err < 1e-6, f"P(k) sum mismatch: rel_err={P_err:.2e}"
    assert D_err < 1e-6, f"D(k) sum mismatch: rel_err={D_err:.2e}"
    assert E_err < 1e-6, f"E(k) sum mismatch: rel_err={E_err:.2e}"
    assert Omega_err < 1e-6, f"Omega(k) sum mismatch: rel_err={Omega_err:.2e}"

    print("  ALL CHECKS PASSED ✓")
    print("=" * 60)

    return P_err, D_err, E_err, Omega_err
