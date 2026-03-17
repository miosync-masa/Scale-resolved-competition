#!/usr/bin/env python3
"""
run_viscosity.py — Fig. 2 data
Taylor-Green at nu=0.02, 0.01, 0.005 (T=4.0) + nu=0.005 extended (T=6.0)
Outputs: data/fig2_viscosity.npz
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic

all_results = {}

for nu_val, T_final in [(0.02, 4.0), (0.01, 4.0), (0.005, 4.0), (0.005, 6.0)]:
    label = f"nu{nu_val}_T{T_final}"
    print("\n" + "=" * 60)
    print(f"  Fig.2: TG nu={nu_val}, T={T_final}")
    print("=" * 60)

    solver = NSSolver(N=128, nu=nu_val, dt=1e-4)
    u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

    result = solver.run(u_hat, v_hat, w_hat, T_final=T_final,
                        diag_interval=100, shell_diag=False, verbose=True)

    all_results[label] = {
        'times': result['times'],
        'Omegas': result['Omegas'],
        'Rs': result['Rs'],
        'Ps': result['Ps'],
        'Ds': result['Ds'],
    }

    print(f"  R_max = {result['Rs'].max():.4f} at t = {result['times'][result['Rs'].argmax()]:.2f}")
    print(f"  Omega_max = {result['Omegas'].max():.4f}")

np.savez('data/fig2_viscosity.npz', **{
    f"{k}_{field}": v[field]
    for k, v in all_results.items()
    for field in ['times', 'Omegas', 'Rs', 'Ps', 'Ds']
})

print("\n  Saved: data/fig2_viscosity.npz")
