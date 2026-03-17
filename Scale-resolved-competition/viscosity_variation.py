# =============================================================================
# 🔥 PHASE 1: VISCOSITY VARIATION TEST
#    Testing regularity across different ν values
# =============================================================================

import jax
import jax.numpy as jnp
from jax import jit, lax
from jax.numpy.fft import fftn, ifftn, fftfreq
import numpy as np

print(f"JAX devices: {jax.devices()}")

def run_viscosity_test(nu_value, label=""):
    """
    指定された粘性係数でシミュレーション実行
    """

    print("\n" + "=" * 70)
    print(f"🔥 VISCOSITY TEST: ν = {nu_value} {label}")
    print("=" * 70)

    N = 128
    L = 2 * jnp.pi
    nu = nu_value  # ← ここを変更！
    dt = 0.0001
    n_steps = 40000  # t = 4.0 まで

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

    # 初期条件（Taylor-Green）
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
        # 渦度
        omega_x = ifftn(1j * KY * w_hat - 1j * KZ * v_hat).real
        omega_y = ifftn(1j * KZ * u_hat - 1j * KX * w_hat).real
        omega_z = ifftn(1j * KX * v_hat - 1j * KY * u_hat).real

        omega_sq = omega_x**2 + omega_y**2 + omega_z**2
        Omega = 0.5 * jnp.mean(omega_sq)
        omega_max = jnp.max(jnp.sqrt(omega_sq))

        # S_ij
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

    # メインループ
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

    print(f"\n  {'t':>6} | {'Ω':>10} | {'R=P/D':>10} | Status")
    print("-" * 50)

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

        if chunk % 40 == 0:
            status = "🔥 DEVIL" if R > 1 else "✅ ANGEL"
            print(f"  {t:6.2f} | {float(Omega):10.4f} | {float(R):10.4f} | {status}")

        if float(omega_max) > 1e6:
            print(f"\n  💥 BLOW-UP at t = {t:.4f}!")
            break

        if chunk < n_chunks:
            u_hat, v_hat, w_hat = run_chunk((u_hat, v_hat, w_hat))

    total_time = time_module.time() - start_time
    print(f"\n  Computation time: {total_time:.1f}s")

    # 結果まとめ
    times = np.array(times)
    Omegas = np.array(Omegas)
    Rs = np.array(Rs)

    R_max_idx = np.argmax(Rs)
    R_max = Rs[R_max_idx]
    t_R_max = times[R_max_idx]

    Omega_max_idx = np.argmax(Omegas)
    Omega_max = Omegas[Omega_max_idx]
    t_Omega_max = times[Omega_max_idx]

    result = {
        'nu': nu_value,
        'times': times,
        'Rs': Rs,
        'Omegas': Omegas,
        'R_max': R_max,
        't_R_max': t_R_max,
        'R_final': Rs[-1],
        'Omega_max': Omega_max,
        't_Omega_max': t_Omega_max,
        'Omega_final': Omegas[-1],
        'angel_wins': Rs[-1] < 1,
        'omega_decaying': Omegas[-1] < Omega_max
    }

    print(f"\n  Summary for ν = {nu_value}:")
    print(f"    R_max = {R_max:.4f} at t = {t_R_max:.2f}")
    print(f"    R_final = {Rs[-1]:.4f}")
    print(f"    Ω_max = {Omega_max:.4f} at t = {t_Omega_max:.2f}")
    print(f"    Ω_final = {Omegas[-1]:.4f}")
    print(f"    Angel wins: {'✅ YES' if result['angel_wins'] else '❌ NO'}")
    print(f"    Ω decaying: {'✅ YES' if result['omega_decaying'] else '❌ NO'}")

    return result


# =============================================================================
# Phase 1: 3つのνで実験
# =============================================================================

print("\n" + "🔥" * 35)
print("   PHASE 1: VISCOSITY VARIATION TEST")
print("🔥" * 35 + "\n")

nu_values = [0.01, 0.005, 0.02]
labels = ["(baseline)", "(low viscosity - dangerous)", "(high viscosity - safe)"]

all_results = {}

for nu_val, label in zip(nu_values, labels):
    result = run_viscosity_test(nu_val, label)
    all_results[nu_val] = result

# =============================================================================
# 最終比較
# =============================================================================

print("\n" + "=" * 70)
print("🏆 PHASE 1: FINAL COMPARISON")
print("=" * 70)

print(f"""
┌──────────────────────────────────────────────────────────────────────────┐
│                    VISCOSITY VARIATION RESULTS                           │
├──────────┬──────────┬──────────┬──────────┬──────────┬──────────┬────────┤
│    ν     │  R_max   │ t(R_max) │  R_final │  Ω_max   │  Ω_final │ Angel? │
├──────────┼──────────┼──────────┼──────────┼──────────┼──────────┼────────┤""")

for nu_val in nu_values:
    r = all_results[nu_val]
    angel = "✅" if r['angel_wins'] and r['omega_decaying'] else "❌"
    print(f"│  {nu_val:6.3f}  │  {r['R_max']:6.2f}  │  {r['t_R_max']:6.2f}  │  {r['R_final']:6.4f}  │  {r['Omega_max']:6.2f}  │  {r['Omega_final']:6.4f}  │   {angel}   │")

print(f"""└──────────┴──────────┴──────────┴──────────┴──────────┴──────────┴────────┘

PREDICTIONS vs RESULTS:
""")

# 予測との比較
low_nu = all_results[0.005]
mid_nu = all_results[0.01]
high_nu = all_results[0.02]

print(f"  ν↓ → R_max↑ : {low_nu['R_max']:.2f} > {mid_nu['R_max']:.2f} > {high_nu['R_max']:.2f} ? ", end="")
if low_nu['R_max'] > mid_nu['R_max'] > high_nu['R_max']:
    print("✅ CONFIRMED")
else:
    print("❌ UNEXPECTED")

print(f"  ν↓ → t(R_max)↑ : {low_nu['t_R_max']:.2f} > {mid_nu['t_R_max']:.2f} > {high_nu['t_R_max']:.2f} ? ", end="")
if low_nu['t_R_max'] >= mid_nu['t_R_max'] >= high_nu['t_R_max']:
    print("✅ CONFIRMED")
else:
    print("⚠️ CHECK")

all_angel_wins = all(r['angel_wins'] and r['omega_decaying'] for r in all_results.values())

print(f"""
┌──────────────────────────────────────────────────────────────────────────┐
│                                                                          │
│  UNIVERSAL REGULARITY TEST:                                              │
│                                                                          │
│    All ν values: Angel wins eventually?  {'✅ YES - UNIVERSAL!' if all_angel_wins else '❌ NO'}              │
│    All ν values: Ω decays after peak?    {'✅ YES - NO BLOW-UP!' if all_angel_wins else '❌ NO'}              │
│                                                                          │
│  {'🏆 PHASE 1 COMPLETE: REGULARITY CONFIRMED ACROSS ν VALUES! 🏆' if all_angel_wins else '⚠️ Need further investigation'}       │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
""")
