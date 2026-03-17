#!/usr/bin/env python3
"""
run_shell_baseline.py — Fig. 3 data
Shell-resolved R(k,t) for baseline Taylor-Green (N=128, nu=0.01, T=5.0)
Outputs: data/fig3_shell_baseline.npz
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic

print("=" * 60)
print("  Fig.3: Shell-resolved R(k,t), baseline TG (nu=0.01)")
print("=" * 60)

solver = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

# shell diagnostics every 500 steps (= 0.05 time units) for manageable data
result = solver.run(u_hat, v_hat, w_hat, T_final=5.0,
                    diag_interval=500, shell_diag=True, verbose=True)

np.savez('data/fig3_shell_baseline.npz',
         times=result['times'],
         Omegas=result['Omegas'],
         Rs=result['Rs'],
         k_shells=result['k_shells'],
         shell_Rk=result['shell_Rk'],
         shell_Pk=result['shell_Pk'],
         shell_Dk=result['shell_Dk'],
         nu=result['nu'], N=result['N'])

print("\n  Saved: data/fig3_shell_baseline.npz")
print(f"  Shell data shape: {result['shell_Rk'].shape}  (n_times x n_shells)")
