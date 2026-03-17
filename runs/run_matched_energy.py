#!/usr/bin/env python3
"""
run_matched_energy.py — Fig. 5 data
Matched-energy comparison: pure TG vs perturbed TG (E0 = 0.5)
Outputs: data/fig5_matched_energy.npz
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from solver.core import NSSolver
from solver.initial_conditions import (
    taylor_green_ic, perturbed_taylor_green_ic, rescale_to_energy
)
from solver.diagnostics import compute_global_metrics, compute_energy_spectrum

target_E = 0.5

# --- Pure Taylor-Green ---
print("=" * 60)
print("  Fig.5a: Pure Taylor-Green (rescaled to E0=0.5)")
print("=" * 60)

solver = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = taylor_green_ic(solver, amplitude=2.0)
u_hat, v_hat, w_hat = rescale_to_energy(solver, u_hat, v_hat, w_hat, target_E)

# initial spectrum
Ek_pure = compute_energy_spectrum(solver, u_hat, v_hat, w_hat)
Omega0_pure, _, D0_pure, _, _ = compute_global_metrics(solver, u_hat, v_hat, w_hat)
print(f"  E0 = {target_E}, Omega0 = {float(Omega0_pure):.4f}, D0 = {float(D0_pure):.6f}")

result_pure = solver.run(u_hat, v_hat, w_hat, T_final=5.0,
                         diag_interval=100, shell_diag=False, verbose=True)

# --- Perturbed Taylor-Green ---
print("\n" + "=" * 60)
print("  Fig.5b: Perturbed Taylor-Green (rescaled to E0=0.5)")
print("=" * 60)

solver2 = NSSolver(N=128, nu=0.01, dt=1e-4)
u_hat, v_hat, w_hat = perturbed_taylor_green_ic(solver2, amplitude=2.0)
u_hat, v_hat, w_hat = rescale_to_energy(solver2, u_hat, v_hat, w_hat, target_E)

Ek_pert = compute_energy_spectrum(solver2, u_hat, v_hat, w_hat)
Omega0_pert, _, D0_pert, _, _ = compute_global_metrics(solver2, u_hat, v_hat, w_hat)
print(f"  E0 = {target_E}, Omega0 = {float(Omega0_pert):.4f}, D0 = {float(D0_pert):.6f}")

result_pert = solver2.run(u_hat, v_hat, w_hat, T_final=5.0,
                          diag_interval=100, shell_diag=False, verbose=True)

# --- Save ---
np.savez('data/fig5_matched_energy.npz',
         # pure TG
         pure_times=result_pure['times'],
         pure_Omegas=result_pure['Omegas'],
         pure_Rs=result_pure['Rs'],
         pure_Ps=result_pure['Ps'],
         pure_Ds=result_pure['Ds'],
         pure_Ek=Ek_pure,
         pure_Omega0=float(Omega0_pure),
         pure_D0=float(D0_pure),
         # perturbed TG
         pert_times=result_pert['times'],
         pert_Omegas=result_pert['Omegas'],
         pert_Rs=result_pert['Rs'],
         pert_Ps=result_pert['Ps'],
         pert_Ds=result_pert['Ds'],
         pert_Ek=Ek_pert,
         pert_Omega0=float(Omega0_pert),
         pert_D0=float(D0_pert),
         # common
         k_shells=np.array(solver.k_shells),
         target_E=target_E)

print("\n  Saved: data/fig5_matched_energy.npz")
print(f"\n  Pure TG:  D0={float(D0_pure):.4f}, R_max={result_pure['Rs'].max():.2f}")
print(f"  Pert TG:  D0={float(D0_pert):.4f}, R_max={result_pert['Rs'].max():.2f}")
print(f"  D0 ratio: {float(D0_pert)/float(D0_pure):.1f}x")
