# =============================================================================
#  core.py — Pseudo-spectral Navier-Stokes solver (JAX)
#
#  Fully dealiased (2/3-rule), RK4 time integration,
#  explicit divergence-free projection after every step.
# =============================================================================

import jax
import jax.numpy as jnp
from jax import jit, lax
from jax.numpy.fft import fftn, ifftn, fftfreq
import numpy as np
import time as time_module


class NSSolver:
    """
    Pseudo-spectral incompressible Navier-Stokes solver on T^3 = [0, 2pi]^3.

    Parameters
    ----------
    N   : int     — grid resolution per side
    nu  : float   — kinematic viscosity
    dt  : float   — time step
    """

    def __init__(self, N=128, nu=0.01, dt=1e-4):
        self.N = N
        self.nu = nu
        self.dt = dt
        self.L = 2.0 * jnp.pi

        # --- wavenumber grid ---
        k1d = fftfreq(N, self.L / (2.0 * jnp.pi * N))
        self.KX, self.KY, self.KZ = jnp.meshgrid(k1d, k1d, k1d, indexing='ij')
        self.K2 = self.KX**2 + self.KY**2 + self.KZ**2
        self.K_mag = jnp.sqrt(self.K2)
        self.K2_safe = jnp.where(self.K2 == 0, 1.0, self.K2)

        # --- dealiasing mask (2/3-rule) ---
        k_max = N // 3
        self.dealias_mask = (
            (jnp.abs(self.KX) < k_max) &
            (jnp.abs(self.KY) < k_max) &
            (jnp.abs(self.KZ) < k_max)
        ).astype(jnp.float32)

        # --- physical grid ---
        x1d = jnp.linspace(0, self.L, N, endpoint=False)
        self.X, self.Y, self.Z = jnp.meshgrid(x1d, x1d, x1d, indexing='ij')

        # --- shell wavenumber array for diagnostics ---
        self.k_shells = jnp.arange(0, int(N * jnp.sqrt(3) / 2) + 2)

        # --- build JIT-compiled functions ---
        self._build_jit_functions()

    # -----------------------------------------------------------------
    #  JIT compilation
    # -----------------------------------------------------------------
    def _build_jit_functions(self):
        KX, KY, KZ = self.KX, self.KY, self.KZ
        K2, K2_safe = self.K2, self.K2_safe
        nu = self.nu
        dt = self.dt
        dealias_mask = self.dealias_mask

        @jit
        def project(u_hat, v_hat, w_hat):
            """Divergence-free projection in Fourier space."""
            k_dot_u = KX * u_hat + KY * v_hat + KZ * w_hat
            up = u_hat - KX * k_dot_u / K2_safe
            vp = v_hat - KY * k_dot_u / K2_safe
            wp = w_hat - KZ * k_dot_u / K2_safe
            up = up.at[0, 0, 0].set(u_hat[0, 0, 0])
            vp = vp.at[0, 0, 0].set(v_hat[0, 0, 0])
            wp = wp.at[0, 0, 0].set(w_hat[0, 0, 0])
            return up, vp, wp

        @jit
        def rk4_step(u_hat, v_hat, w_hat):
            """Single RK4 step + projection."""
            def rhs(uh, vh, wh):
                u = ifftn(uh).real
                v = ifftn(vh).real
                w = ifftn(wh).real

                dudx = ifftn(1j * KX * uh).real
                dudy = ifftn(1j * KY * uh).real
                dudz = ifftn(1j * KZ * uh).real
                dvdx = ifftn(1j * KX * vh).real
                dvdy = ifftn(1j * KY * vh).real
                dvdz = ifftn(1j * KZ * vh).real
                dwdx = ifftn(1j * KX * wh).real
                dwdy = ifftn(1j * KY * wh).real
                dwdz = ifftn(1j * KZ * wh).real

                nl_u = u * dudx + v * dudy + w * dudz
                nl_v = u * dvdx + v * dvdy + w * dvdz
                nl_w = u * dwdx + v * dwdy + w * dwdz

                nl_u_h = fftn(nl_u) * dealias_mask
                nl_v_h = fftn(nl_v) * dealias_mask
                nl_w_h = fftn(nl_w) * dealias_mask

                div_nl = 1j * KX * nl_u_h + 1j * KY * nl_v_h + 1j * KZ * nl_w_h
                p_hat = -div_nl / K2_safe
                p_hat = p_hat.at[0, 0, 0].set(0)

                return (-nl_u_h - 1j * KX * p_hat - nu * K2 * uh,
                        -nl_v_h - 1j * KY * p_hat - nu * K2 * vh,
                        -nl_w_h - 1j * KZ * p_hat - nu * K2 * wh)

            k1 = rhs(u_hat, v_hat, w_hat)
            k2 = rhs(u_hat + 0.5 * dt * k1[0],
                      v_hat + 0.5 * dt * k1[1],
                      w_hat + 0.5 * dt * k1[2])
            k3 = rhs(u_hat + 0.5 * dt * k2[0],
                      v_hat + 0.5 * dt * k2[1],
                      w_hat + 0.5 * dt * k2[2])
            k4 = rhs(u_hat + dt * k3[0],
                      v_hat + dt * k3[1],
                      w_hat + dt * k3[2])

            u_new = u_hat + dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
            v_new = v_hat + dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
            w_new = w_hat + dt / 6 * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2])

            return project(u_new, v_new, w_new)

        @jit
        def run_chunk(state, chunk_size=100):
            """Advance chunk_size steps without diagnostics."""
            def body_fn(carry, _):
                return rk4_step(*carry), None
            (uh, vh, wh), _ = lax.scan(body_fn, state, None, length=chunk_size)
            return uh, vh, wh

        self.project = project
        self.rk4_step = rk4_step
        self.run_chunk = run_chunk

    # -----------------------------------------------------------------
    #  Warmup
    # -----------------------------------------------------------------
    def warmup(self, u_hat, v_hat, w_hat):
        """JIT warmup calls."""
        from .diagnostics import compute_global_metrics, compute_shell_metrics
        _ = compute_global_metrics(self, u_hat, v_hat, w_hat)
        _ = compute_shell_metrics(self, u_hat, v_hat, w_hat)
        _ = self.run_chunk((u_hat, v_hat, w_hat))

    # -----------------------------------------------------------------
    #  Main simulation loop
    # -----------------------------------------------------------------
    def run(self, u_hat, v_hat, w_hat, T_final,
            diag_interval=100, shell_diag=False, verbose=True):
        """
        Run simulation from t=0 to t=T_final.

        Parameters
        ----------
        T_final        : float — end time
        diag_interval  : int   — steps between diagnostics
        shell_diag     : bool  — also compute shell-resolved R(k,t)
        verbose        : bool  — print progress

        Returns
        -------
        dict with time series of all diagnostics and final state.
        """
        from .diagnostics import compute_global_metrics, compute_shell_metrics

        n_steps = int(round(T_final / self.dt))
        n_chunks = n_steps // diag_interval

        # project initial condition
        u_hat, v_hat, w_hat = self.project(u_hat, v_hat, w_hat)

        # warmup
        if verbose:
            print("  JIT warmup ...")
        self.warmup(u_hat, v_hat, w_hat)

        # storage
        times, Omegas, Ps, Ds, Rs = [], [], [], [], []
        shell_Rk = [] if shell_diag else None
        shell_Pk = [] if shell_diag else None
        shell_Dk = [] if shell_diag else None

        if verbose:
            print(f"\n  {'t':>6} | {'Omega':>10} | {'P':>12} | {'D':>12} | {'R=P/D':>10}")
            print("-" * 65)

        t0 = time_module.time()

        for chunk in range(n_chunks + 1):
            step = chunk * diag_interval
            t = step * self.dt

            Omega, P, D, R, omega_max = compute_global_metrics(
                self, u_hat, v_hat, w_hat)

            times.append(float(t))
            Omegas.append(float(Omega))
            Ps.append(float(P))
            Ds.append(float(D))
            Rs.append(float(R))

            if shell_diag:
                Pk_arr, Dk_arr, Rk_arr = compute_shell_metrics(
                    self, u_hat, v_hat, w_hat)
                shell_Pk.append(np.array(Pk_arr))
                shell_Dk.append(np.array(Dk_arr))
                shell_Rk.append(np.array(Rk_arr))

            if verbose and (chunk % max(1, n_chunks // 20) == 0):
                status = "PROD" if R > 1 else "DISS"
                print(f"  {t:6.2f} | {float(Omega):10.4f} | "
                      f"{float(P):+12.6f} | {float(D):12.6f} | "
                      f"{float(R):10.4f} | {status}")

            if float(omega_max) > 1e6:
                print(f"\n  BLOW-UP at t = {t:.4f}!")
                break

            if chunk < n_chunks:
                u_hat, v_hat, w_hat = self.run_chunk(
                    (u_hat, v_hat, w_hat), chunk_size=diag_interval)

        wall = time_module.time() - t0
        if verbose:
            print(f"\n  Wall time: {wall:.1f}s")

        result = {
            'times': np.array(times),
            'Omegas': np.array(Omegas),
            'Ps': np.array(Ps),
            'Ds': np.array(Ds),
            'Rs': np.array(Rs),
            'nu': self.nu,
            'N': self.N,
            'dt': self.dt,
            'state': (u_hat, v_hat, w_hat),
        }
        if shell_diag:
            result['shell_Pk'] = np.array(shell_Pk)
            result['shell_Dk'] = np.array(shell_Dk)
            result['shell_Rk'] = np.array(shell_Rk)
            result['k_shells'] = np.array(self.k_shells)

        return result
