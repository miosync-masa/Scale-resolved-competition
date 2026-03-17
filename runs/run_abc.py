#!/usr/bin/env python3
"""
run_abc.py — Fig. 6 data
Geometry effect: Taylor-Green vs ABC/Beltrami (N=128, nu=0.01, T=5.0)
Outputs: data/fig6_abc.npz
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic, abc_ic

# --- Taylor-Green ---
print("=" * 60)
print("  Fig.6a: Taylor-Green (N=128, nu=0.01)")
print("=" * 60)

solver = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

result_tg = solver.run(u_hat, v_hat, w_hat, T_final=5.0,
                       diag_interval=100, shell_diag=False, verbose=True)

# --- ABC ---
print("\n" + "=" * 60)
print("  Fig.6b: ABC/Beltrami (A=B=C=1, N=128, nu=0.01)")
print("=" * 60)

solver2 = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = abc_ic(solver2, A_coeff=1.0, B_coeff=1.0, C_coeff=1.0)

result_abc = solver2.run(u_hat, v_hat, w_hat, T_final=5.0,
                         diag_interval=100, shell_diag=False, verbose=True)

# --- Save ---
np.savez('data/fig6_abc.npz',
         tg_times=result_tg['times'],
         tg_Omegas=result_tg['Omegas'],
         tg_Rs=result_tg['Rs'],
         tg_Ps=result_tg['Ps'],
         tg_Ds=result_tg['Ds'],
         abc_times=result_abc['times'],
         abc_Omegas=result_abc['Omegas'],
         abc_Rs=result_abc['Rs'],
         abc_Ps=result_abc['Ps'],
         abc_Ds=result_abc['Ds'])

print("\n  Saved: data/fig6_abc.npz")
print(f"\n  TG:   R_max={result_tg['Rs'].max():.4f}, Omega_max={result_tg['Omegas'].max():.4f}")
print(f"  ABC:  R_max={result_abc['Rs'].max():.6f}, Omega_max={result_abc['Omegas'].max():.4f}")
