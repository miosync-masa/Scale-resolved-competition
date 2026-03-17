#!/usr/bin/env python3
"""
run_highre.py — High-Reynolds-number validation runs
N=256, nu=0.002 and nu=0.001, with shell-resolved diagnostics.

Designed to run overnight on H100.
Outputs: data/highre_nu0002.npz, data/highre_nu0001.npz

Usage on Colab:
  !nohup python runs/run_highre.py > highre_log.txt 2>&1 &
  (then close laptop and sleep)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import time as time_module

# --- Override solver defaults for N=256 ---
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic

os.makedirs('data', exist_ok=True)

runs = [
    {'nu': 0.002, 'T': 6.0, 'label': 'nu0002'},
    {'nu': 0.001, 'T': 6.0, 'label': 'nu0001'},
]

for run in runs:
    nu_val = run['nu']
    T_final = run['T']
    label = run['label']

    print("\n" + "=" * 70)
    print(f"  HIGH-RE RUN: N=256, nu={nu_val}, T={T_final}")
    print(f"  Estimated Re ~ {int(2.0 / nu_val)}")
    print("=" * 70)

    t_start = time_module.time()

    # N=256, smaller dt for stability
    solver = NSSolver(N=256, nu=nu_val, dt=5e-5)
    u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

    # shell diagnostics every 1000 steps (= 0.05 time units)
    result = solver.run(u_hat, v_hat, w_hat, T_final=T_final,
                        diag_interval=1000, shell_diag=True, verbose=True)

    outfile = f'data/highre_{label}.npz'
    np.savez(outfile,
             times=result['times'],
             Omegas=result['Omegas'],
             Ps=result['Ps'],
             Ds=result['Ds'],
             Rs=result['Rs'],
             k_shells=result['k_shells'],
             shell_Rk=result['shell_Rk'],
             shell_Pk=result['shell_Pk'],
             shell_Dk=result['shell_Dk'],
             nu=result['nu'], N=result['N'])

    elapsed = time_module.time() - t_start

    print(f"\n  Saved: {outfile}")
    print(f"  R_max = {result['Rs'].max():.4f} at t = {result['times'][result['Rs'].argmax()]:.2f}")
    print(f"  Omega_max = {result['Omegas'].max():.4f} at t = {result['times'][result['Omegas'].argmax()]:.2f}")
    print(f"  R(T) = {result['Rs'][-1]:.4f}")
    print(f"  Omega(T) = {result['Omegas'][-1]:.4f}")
    print(f"  Wall time: {elapsed/3600:.1f} hours")
    print(f"  Shell data shape: {result['shell_Rk'].shape}")

print("\n" + "=" * 70)
print("  ALL HIGH-RE RUNS COMPLETE!")
print("=" * 70)
