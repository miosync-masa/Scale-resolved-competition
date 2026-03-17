# Scale-resolved competition between vortex stretching and viscous dissipation in three-dimensional Navier–Stokes flow

Pseudo-spectral DNS code for the paper submitted to the *Journal of Fluid Mechanics*:

**"Scale-resolved competition between vortex stretching and viscous dissipation in three-dimensional Navier–Stokes flow"**


## Overview

This repository provides a fully dealiased pseudo-spectral Navier–Stokes solver (JAX/GPU) together with all simulation scripts and figure-generation code used in the paper. The central diagnostic is the exact enstrophy budget

dΩ/dt = P − D

analysed through the global stretching-to-dissipation ratio R(t) = P(t)/D(t) and its shell-resolved counterpart R(k,t).

## Structure

```
solver/
  core.py                 ← NS solver engine (RK4, projection, dealiasing)
  diagnostics.py          ← Global (Ω,P,D,R) + shell-resolved R(k,t)
  initial_conditions.py   ← Taylor-Green, perturbed TG, ABC/Beltrami

runs/
  run_baseline.py         → Fig.1 data (baseline TG, N=128, ν=0.01)
  run_viscosity.py        → Fig.2 data (ν = 0.02, 0.01, 0.005)
  run_shell_baseline.py   → Fig.3 data (shell-resolved R(k,t))
  run_shell_lowvis.py     → Fig.4 data (ν=0.005, T=6, shell-resolved)
  run_matched_energy.py   → Fig.5 data (pure TG vs perturbed TG, E₀=0.5)
  run_abc.py              → Fig.6 data (TG vs ABC/Beltrami)
  run_highre_safe.sh      → High-Re validation (N=256, overnight runs)
  run_highre_single.py    → Single high-Re run (called by safe.sh)

figures/
  generate_all_figures.py ← All 6 JFM figures (vector PDF)
  generate_movie.py       ← Supplementary Movie 1 (R(k,t) animation)

data/                     ← .npz output (created by runs)
run_all.sh                ← One-shot execution script
```

## Quick start (Google Colab + GPU)

```python
# 1. Clone
!git clone https://github.com/miosync-masa/Scale-resolved-competition.git
%cd Scale-resolved-competition

# 2. Install JAX with GPU
!pip install jax[cuda12]

# 3. Run all paper figures
!bash run_all.sh

# 4. Generate figures
!python figures/generate_all_figures.py
```

## Requirements

- JAX (with GPU for speed; H100/A100 recommended)
- NumPy
- Matplotlib

## Summary of results

### Paper runs (N=128)

| ν | Re | R_max | t(R_max) | Ω_max | t(Ω_max) | R(T) | Ω(T) |
|---|---|---|---|---|---|---|---|
| 0.020 | ~100 | 2.78 | 0.69 | 2.59 | 2.44 | 0.62 | 1.74 |
| 0.010 | ~200 | 5.67 | 0.68 | 5.11 | 2.99 | 0.71 | 2.82 |
| 0.005 | ~400 | 11.46 | 0.67 | 8.74 | 3.32 | 0.63 | 4.91 |

### High-Reynolds-number validation (N=256, post-submission)

Additional runs at higher Reynolds number were performed after submission to verify that the dissipative-dominance scenario persists at higher Re. These runs use N=256 grid resolution with shell-resolved diagnostics.

| ν | Re | R_max | t(R_max) | Ω_max | R(6.0) | Outcome |
|---|---|---|---|---|---|---|
| 0.002 | ~1000 | 28.80 | 0.60 | 24.09 | 0.77 | Dissipation wins |
| 0.001 | ~2000 | 57.71 | 0.60 | 53.05 | 0.84 | Dissipation wins |

**Key observations from the high-Re runs:**

1. **R_max scales strongly with decreasing ν** — the peak stretching-to-dissipation ratio reaches 57.7 at Re~2000 — yet the global ratio still falls below unity by t=6.0 in all cases.

2. **Brief re-intensification at ν=0.001** — at t≈5.1, R briefly returns above unity (R=1.0096) before falling back, consistent with the intermittent crossover behaviour observed at ν=0.005 in the paper. No persistent production corridor is formed.

3. **The k⁴ dissipative barrier remains intact** — despite the dramatically larger peak ratios, the qualitative scenario (advance → saturation → recession of the stretching-dominated spectral band) is preserved at Re~2000.

These results support the paper's central conclusion: vortex stretching can be intense and spectrally mobile, but its dominance is transient, and the enstrophy budget eventually becomes controlled by viscous dissipation.

To reproduce:
```python
!bash runs/run_highre_safe.sh
```

## Figure mapping

| Figure | Script | Description |
|--------|--------|-------------|
| Fig.1 | run_baseline.py | Baseline TG global budget (Ω, P, D, R) |
| Fig.2 | run_viscosity.py | Viscosity dependence (ν sweep) |
| Fig.3 | run_shell_baseline.py | Shell-resolved R(k,t) heatmap |
| Fig.4 | run_shell_lowvis.py | Low-ν long-time R(k,t) + cascade front |
| Fig.5 | run_matched_energy.py | Dissipation pre-payment effect |
| Fig.6 | run_abc.py | Geometry effect: TG vs ABC |
| Movie 1 | generate_movie.py | R(k,t) time evolution animation |

## License

MIT

## Citation

If you use this code, please cite the associated paper (submitted to JFM, 2026).
