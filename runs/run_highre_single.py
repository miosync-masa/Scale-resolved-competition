#!/usr/bin/env python3
"""
run_highre_single.py — Single high-Re run (N=256)
Usage: python runs/run_highre_single.py --nu 0.002 --label nu0002
"""
import sys, os, argparse
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import taylor_green_ic
import time as time_module

parser = argparse.ArgumentParser()
parser.add_argument('--nu', type=float, required=True)
parser.add_argument('--label', type=str, required=True)
parser.add_argument('--T', type=float, default=6.0)
args = parser.parse_args()

os.makedirs('data', exist_ok=True)

print(f"\n  HIGH-RE: N=256, nu={args.nu}, T={args.T}, Re~{int(2.0/args.nu)}")

t_start = time_module.time()

solver = NSSolver(N=256, nu=args.nu, dt=5e-5)
u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)

result = solver.run(u_hat, v_hat, w_hat, T_final=args.T,
                    diag_interval=1000, shell_diag=True, verbose=True)

outfile = f'data/highre_{args.label}.npz'
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
print(f"  R_max = {result['Rs'].max():.4f}")
print(f"  Omega_max = {result['Omegas'].max():.4f}")
print(f"  R(T) = {result['Rs'][-1]:.4f}")
print(f"  Wall time: {elapsed/3600:.1f} hours")
