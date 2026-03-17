# =============================================================================
# 🔥 LONG-TIME CASCADE TRACKING
#    Does the "devil wave" eventually stop?
# =============================================================================

import jax
import jax.numpy as jnp
from jax import jit, lax
from jax.numpy.fft import fftn, ifftn, fftfreq
import numpy as np

print(f"JAX devices: {jax.devices()}")

def run_long_time_cascade():
    """
    長時間シミュレーション
    カスケードの前線が止まるか確認
    """

    print("=" * 70)
    print("🔥 LONG-TIME CASCADE TRACKING")
    print("   Does the devil wave eventually stop?")
    print("=" * 70)

    N = 128
    L = 2 * jnp.pi
    nu = 0.005
    dt = 0.0001
    n_steps = 60000  # t = 2.0 まで！

    # 波数
    kx = fftfreq(N, L / (2 * jnp.pi * N))
    ky = fftfreq(N, L / (2 * jnp.pi * N))
    kz = fftfreq(N, L / (2 * jnp.pi * N))
    KX, KY, KZ = jnp.meshgrid(kx, ky, kz, indexing='ij')
    K2 = KX**2 + KY**2 + KZ**2
    K_mag = jnp.sqrt(K2)
    K2_safe = jnp.where(K2 == 0, 1.0, K2)

    k_max = N // 3
    dealias_mask = ((jnp.abs(KX) < k_max) &
                    (jnp.abs(KY) < k_max) &
                    (jnp.abs(KZ) < k_max)).astype(jnp.float32)

    print(f"\n  N={N}, ν={nu}, dt={dt}")
    print(f"  Total time: t = {n_steps * dt}")

    # 初期条件
    x = jnp.linspace(0, L, N, endpoint=False)
    y = jnp.linspace(0, L, N, endpoint=False)
    z = jnp.linspace(0, L, N, endpoint=False)
    X, Y, Z = jnp.meshgrid(x, y, z, indexing='ij')

    amplitude = 2.0
    u_hat = fftn(amplitude * jnp.sin(X) * jnp.cos(Y) * jnp.cos(Z))
    v_hat = fftn(-amplitude * jnp.cos(X) * jnp.sin(Y) * jnp.cos(Z))
    w_hat = fftn(jnp.zeros_like(X))

    @jit
    def project_divergence_free(u_hat, v_hat, w_hat):
        k_dot_u = KX * u_hat + KY * v_hat + KZ * w_hat
        u_hat_proj = u_hat - KX * k_dot_u / K2_safe
        v_hat_proj = v_hat - KY * k_dot_u / K2_safe
        w_hat_proj = w_hat - KZ * k_dot_u / K2_safe
        u_hat_proj = u_hat_proj.at[0,0,0].set(u_hat[0,0,0])
        v_hat_proj = v_hat_proj.at[0,0,0].set(v_hat[0,0,0])
        w_hat_proj = w_hat_proj.at[0,0,0].set(w_hat[0,0,0])
        return u_hat_proj, v_hat_proj, w_hat_proj

    @jit
    def compute_global_metrics(u_hat, v_hat, w_hat):
        """グローバルなΩ, P, D, Rを計算"""
        # 渦度
        omega_x = ifftn(1j * KY * w_hat - 1j * KZ * v_hat).real
        omega_y = ifftn(1j * KZ * u_hat - 1j * KX * w_hat).real
        omega_z = ifftn(1j * KX * v_hat - 1j * KY * u_hat).real

        omega_sq = omega_x**2 + omega_y**2 + omega_z**2
        Omega = 0.5 * jnp.mean(omega_sq)
        omega_max = jnp.max(jnp.sqrt(omega_sq))

        # S_ij (trace-free)
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
        S_zz = -(S_xx + S_yy)
        S_xy = 0.5 * (dudy + dvdx)
        S_xz = 0.5 * (dudz + dwdx)
        S_yz = 0.5 * (dvdz + dwdy)

        # P
        omega_S_omega = (
            omega_x * (S_xx * omega_x + S_xy * omega_y + S_xz * omega_z) +
            omega_y * (S_xy * omega_x + S_yy * omega_y + S_yz * omega_z) +
            omega_z * (S_xz * omega_x + S_yz * omega_y + S_zz * omega_z)
        )
        P = jnp.mean(omega_S_omega)

        # D
        omega_x_hat = fftn(omega_x)
        omega_y_hat = fftn(omega_y)
        omega_z_hat = fftn(omega_z)

        grad_omega_sq = jnp.zeros_like(omega_x)
        for omega_hat in [omega_x_hat, omega_y_hat, omega_z_hat]:
            for K_comp in [KX, KY, KZ]:
                grad_omega_sq += ifftn(1j * K_comp * omega_hat).real**2

        D = nu * jnp.mean(grad_omega_sq)

        R = P / (D + 1e-15)

        return Omega, P, D, R, omega_max

    @jit
    def rk4_step_with_projection(u_hat, v_hat, w_hat):
        def ns_rhs(u_hat, v_hat, w_hat):
            u = ifftn(u_hat).real
            v = ifftn(v_hat).real
            w = ifftn(w_hat).real

            dudx = ifftn(1j * KX * u_hat).real
            dudy = ifftn(1j * KY * u_hat).real
            dudz = ifftn(1j * KZ * u_hat).real
            dvdx = ifftn(1j * KX * v_hat).real
            dvdy = ifftn(1j * KY * v_hat).real
            dvdz = ifftn(1j * KZ * v_hat).real
            dwdx = ifftn(1j * KX * w_hat).real
            dwdy = ifftn(1j * KY * w_hat).real
            dwdz = ifftn(1j * KZ * w_hat).real

            nl_u = u * dudx + v * dudy + w * dudz
            nl_v = u * dvdx + v * dvdy + w * dvdz
            nl_w = u * dwdx + v * dwdy + w * dwdz

            nl_u_hat = fftn(nl_u) * dealias_mask
            nl_v_hat = fftn(nl_v) * dealias_mask
            nl_w_hat = fftn(nl_w) * dealias_mask

            div_nl = 1j * KX * nl_u_hat + 1j * KY * nl_v_hat + 1j * KZ * nl_w_hat
            p_hat = -div_nl / K2_safe
            p_hat = p_hat.at[0, 0, 0].set(0)

            return (-nl_u_hat - 1j*KX*p_hat - nu*K2*u_hat,
                    -nl_v_hat - 1j*KY*p_hat - nu*K2*v_hat,
                    -nl_w_hat - 1j*KZ*p_hat - nu*K2*w_hat)

        k1 = ns_rhs(u_hat, v_hat, w_hat)
        k2 = ns_rhs(u_hat + 0.5*dt*k1[0], v_hat + 0.5*dt*k1[1], w_hat + 0.5*dt*k1[2])
        k3 = ns_rhs(u_hat + 0.5*dt*k2[0], v_hat + 0.5*dt*k2[1], w_hat + 0.5*dt*k2[2])
        k4 = ns_rhs(u_hat + dt*k3[0], v_hat + dt*k3[1], w_hat + dt*k3[2])

        u_new = u_hat + dt/6*(k1[0] + 2*k2[0] + 2*k3[0] + k4[0])
        v_new = v_hat + dt/6*(k1[1] + 2*k2[1] + 2*k3[1] + k4[1])
        w_new = w_hat + dt/6*(k1[2] + 2*k2[2] + 2*k3[2] + k4[2])

        return project_divergence_free(u_new, v_new, w_new)

    @jit
    def run_chunk(state):
        def body_fn(carry, _):
            return rk4_step_with_projection(*carry), None
        (u_hat, v_hat, w_hat), _ = lax.scan(body_fn, state, None, length=100)
        return u_hat, v_hat, w_hat

    # =========================================================================
    # メインループ
    # =========================================================================

    print("\n" + "=" * 70)
    print("🚀 LONG-TIME EVOLUTION")
    print("=" * 70)

    u_hat, v_hat, w_hat = project_divergence_free(u_hat, v_hat, w_hat)

    # JITウォームアップ
    _ = compute_global_metrics(u_hat, v_hat, w_hat)
    _ = run_chunk((u_hat, v_hat, w_hat))

    times = []
    Omegas = []
    Rs = []
    Ps = []
    Ds = []

    import time as time_module
    start_time = time_module.time()

    print(f"\n  {'t':>6} | {'Ω':>10} | {'P':>12} | {'D':>12} | {'R=P/D':>10} | Status")
    print("-" * 75)

    n_chunks = n_steps // 100

    for chunk in range(n_chunks + 1):
        step = chunk * 100
        t = step * dt

        Omega, P, D, R, omega_max = compute_global_metrics(u_hat, v_hat, w_hat)

        times.append(float(t))
        Omegas.append(float(Omega))
        Ps.append(float(P))
        Ds.append(float(D))
        Rs.append(float(R))

        if chunk % 20 == 0:
            status = "🔥 DEVIL" if R > 1 else "✅ ANGEL"
            trend = ""
            if len(Rs) > 1:
                if Rs[-1] > Rs[-2]:
                    trend = "↑"
                else:
                    trend = "↓"

            print(f"  {t:6.2f} | {float(Omega):10.4f} | {float(P):+12.6f} | "
                  f"{float(D):12.6f} | {float(R):10.4f} | {status} {trend}")

        if float(omega_max) > 1e6:
            print(f"\n  💥 BLOW-UP at t = {t:.4f}!")
            break

        if chunk < n_chunks:
            u_hat, v_hat, w_hat = run_chunk((u_hat, v_hat, w_hat))

    total_time = time_module.time() - start_time
    print(f"\n  Total computation: {total_time:.1f}s")

    # =========================================================================
    # 解析
    # =========================================================================

    print("\n" + "=" * 70)
    print("📊 LONG-TIME ANALYSIS")
    print("=" * 70)

    times = np.array(times)
    Omegas = np.array(Omegas)
    Rs = np.array(Rs)

    # Rのピークを見つける
    R_max_idx = np.argmax(Rs)
    R_max = Rs[R_max_idx]
    t_R_max = times[R_max_idx]

    print(f"\n  【1】R = P/D Evolution")
    print(f"      R_max = {R_max:.4f} at t = {t_R_max:.2f}")
    print(f"      R_final = {Rs[-1]:.4f} at t = {times[-1]:.2f}")

    # Rが1を下回った時刻
    R_below_1_times = times[Rs < 1]
    if len(R_below_1_times) > 0:
        t_angel_wins = R_below_1_times[0]
        print(f"      Angel wins (R<1) first at t = {t_angel_wins:.2f}")
    else:
        print(f"      Angel never won (R>1 throughout)")

    # Ωの挙動
    print(f"\n  【2】Enstrophy Ω Evolution")
    Omega_max_idx = np.argmax(Omegas)
    print(f"      Ω_initial = {Omegas[0]:.4f}")
    print(f"      Ω_max = {Omegas[Omega_max_idx]:.4f} at t = {times[Omega_max_idx]:.2f}")
    print(f"      Ω_final = {Omegas[-1]:.4f}")

    if Omegas[-1] < Omegas[Omega_max_idx]:
        print(f"      → Ω peaked and is now DECAYING ✅")
    else:
        print(f"      → Ω still growing ⚠️")

    # =========================================================================
    # 最終判定
    # =========================================================================

    print("\n" + "=" * 70)
    print("🏆 MILLENNIUM VERDICT")
    print("=" * 70)

    angel_final_win = Rs[-1] < 1
    omega_decaying = Omegas[-1] < Omegas[Omega_max_idx]

    print(f"""
    ┌────────────────────────────────────────────────────────────────────┐
    │                                                                    │
    │  LONG-TIME SIMULATION RESULTS (t = 0 → {times[-1]:.1f})                    │
    │                                                                    │
    │  R = P/D (Devil vs Angel):                                        │
    │    Peak: R_max = {R_max:.2f} at t = {t_R_max:.2f}                              │
    │    Final: R = {Rs[-1]:.4f}                                             │
    │    {"✅ ANGEL WINS EVENTUALLY!" if angel_final_win else "🔥 Devil still winning..."}                              │
    │                                                                    │
    │  Enstrophy Ω:                                                      │
    │    Peak: Ω_max = {Omegas[Omega_max_idx]:.2f} at t = {times[Omega_max_idx]:.2f}                            │
    │    Final: Ω = {Omegas[-1]:.4f}                                             │
    │    {"✅ DECAYING - No blow-up!" if omega_decaying else "⚠️ Still growing"}                              │
    │                                                                    │
    │  CONCLUSION:                                                       │
    │    {"Viscous dissipation eventually dominates!" if angel_final_win and omega_decaying else "Need longer simulation"}                │
    │    {"R peaks and then falls below 1" if angel_final_win else ""}                          │
    │    {"Ω peaks and then decays" if omega_decaying else ""}                                   │
    │    {"This is the REGULARITY MECHANISM!" if angel_final_win and omega_decaying else ""}                      │
    │                                                                    │
    └────────────────────────────────────────────────────────────────────┘
    """)

    return {
        'times': times,
        'Rs': Rs,
        'Omegas': Omegas,
        'R_max': R_max,
        't_R_max': t_R_max
    }


# =============================================================================
# 実行！
# =============================================================================
print("\n" + "🔥" * 35)
print("   LONG-TIME CASCADE TRACKING")
print("🔥" * 35 + "\n")

results = run_long_time_cascade()
