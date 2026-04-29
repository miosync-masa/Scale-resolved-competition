# =============================================================================
#  diagnostics.py — Global and shell-resolved enstrophy budget diagnostics
#
#  Global:  Omega(t), P(t), D(t), R(t) = P/D
#  Shell:   P(k,t), D(k,t), R(k,t) = P(k)/D(k)
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
    D(k) = nu * sum_{kappa in K_k} |kappa|^2 |omega_hat(kappa)|^2
    R(k) = P(k) / D(k)
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

    Pk = np.zeros(n_shells)
    Dk = np.zeros(n_shells)

    for k_idx in range(n_shells):
        k_val = int(k_shells[k_idx])
        mask = (shell_idx == k_val)
        if not np.any(mask):
            continue

        # P(k) = Re[ sum_{kappa in shell} conj(omega_hat_k) . stretch_hat_k ] / (N3 * N3)
        Pk[k_idx] = np.real(
            np.sum(
                np.conj(omega_x_hat_np[mask]) * stretch_x_hat_np[mask] +
                np.conj(omega_y_hat_np[mask]) * stretch_y_hat_np[mask] +
                np.conj(omega_z_hat_np[mask]) * stretch_z_hat_np[mask]
            )
        ) / (N3 * N3)

        # D(k) = nu * sum_{kappa in shell} |kappa|^2 |omega_hat(kappa)|^2 / (N3 * N3)
        omega_sq_shell = (
            np.abs(omega_x_hat_np[mask])**2 +
            np.abs(omega_y_hat_np[mask])**2 +
            np.abs(omega_z_hat_np[mask])**2
        )
        Dk[k_idx] = nu * np.sum(K2_np[mask] * omega_sq_shell) / (N3 * N3)

    Omega_k = np.sum(np.abs(omega_x_hat_np[mask])**2 + 
                  np.abs(omega_y_hat_np[mask])**2 + 
                  np.abs(omega_z_hat_np[mask])**2) / (N3 * N3)
    # R(k) only meaningful where shell has significant enstrophy
    Rk = np.where(Dk > 1e-30, Pk / Dk, np.nan)

    return Pk, Dk, Rk


def compute_energy_spectrum(solver, u_hat, v_hat, w_hat):
    """Compute shell-averaged energy spectrum E(k)."""
    K_mag_np = np.array(solver.K_mag)
    shell_idx = np.round(K_mag_np).astype(int)
    N3 = solver.N ** 3

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
        ) / N3

    return Ek

def verify_shell_sum(solver, u_hat, v_hat, w_hat):
    """Verify Σ P(k) = P_global and Σ D(k) = D_global."""
    Omega, P_global, D_global, _, _ = compute_global_metrics(solver, u_hat, v_hat, w_hat)
    Pk, Dk, _ = compute_shell_metrics(solver, u_hat, v_hat, w_hat)
    
    P_sum = np.sum(Pk)
    D_sum = np.sum(Dk)
    
    P_err = abs(P_sum - float(P_global)) / (abs(float(P_global)) + 1e-30)
    D_err = abs(D_sum - float(D_global)) / (abs(float(D_global)) + 1e-30)
    
    print(f"P: global={float(P_global):.10e}, sum={P_sum:.10e}, rel_err={P_err:.2e}")
    print(f"D: global={float(D_global):.10e}, sum={D_sum:.10e}, rel_err={D_err:.2e}")
    
    assert P_err < 1e-6, f"P(k) sum mismatch: {P_err}"
    assert D_err < 1e-6, f"D(k) sum mismatch: {D_err}"
    return P_err, D_err
