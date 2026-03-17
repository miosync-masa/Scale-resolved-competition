#!/usr/bin/env python3
"""
run_baseline.py — Fig. 1 data
Baseline Taylor-Green at N=128, nu=0.01, T=5.0
Outputs: data/fig1_baseline.npz
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic

print("=" * 60)
print("  Fig.1: Baseline Taylor-Green (N=128, nu=0.01, T=5.0)")
print("=" * 60)

solver = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

result = solver.run(u_hat, v_hat, w_hat, T_final=5.0,
                    diag_interval=100, shell_diag=False, verbose=True)

np.savez('data/fig1_baseline.npz',
         times=result['times'],
         Omegas=result['Omegas'],
         Ps=result['Ps'],
         Ds=result['Ds'],
         Rs=result['Rs'],
         nu=result['nu'], N=result['N'])

print("\n  Saved: data/fig1_baseline.npz")
print(f"  R_max = {result['Rs'].max():.4f} at t = {result['times'][result['Rs'].argmax()]:.2f}")
print(f"  Omega_max = {result['Omegas'].max():.4f} at t = {result['times'][result['Omegas'].argmax()]:.2f}")
