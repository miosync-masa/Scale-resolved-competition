# Scale-resolved competition: Navier-Stokes enstrophy budget

Pseudo-spectral DNS code for the paper:
**"Scale-resolved competition between vortex stretching and viscous dissipation
in three-dimensional Navier-Stokes flow"**

## Structure

```
solver/
  core.py                 ← NS solver engine (RK4, projection, dealiasing)
  diagnostics.py          ← Global (Ω,P,D,R) + shell-resolved R(k,t)
  initial_conditions.py   ← Taylor-Green, perturbed TG, ABC/Beltrami

runs/
  run_baseline.py         → Fig.1 data
  run_viscosity.py        → Fig.2 data (ν = 0.02, 0.01, 0.005)
  run_shell_baseline.py   → Fig.3 data (shell-resolved R(k,t))
  run_shell_lowvis.py     → Fig.4 data (ν=0.005, T=6, shell-resolved)
  run_matched_energy.py   → Fig.5 data (pure TG vs perturbed TG, E₀=0.5)
  run_abc.py              → Fig.6 data (TG vs ABC/Beltrami)

figures/
  generate_all_figures.py ← All 6 JFM figures (vector PDF)

data/                     ← .npz output (created by runs)
run_all.sh                ← One-shot execution script
```

## Quick start (Google Colab + A100)

```python
# 1. Upload or clone this directory
# 2. Install JAX with GPU
!pip install jax[cuda12]

# 3. Run everything
!bash run_all.sh

# Or run individually:
!python runs/run_baseline.py
!python figures/generate_all_figures.py
```

## Requirements

- JAX (with GPU for speed)
- NumPy
- Matplotlib

## Figure mapping

| Figure | Script | Description |
|--------|--------|-------------|
| Fig.1  | run_baseline.py | Baseline TG global budget (Ω, P, D, R) |
| Fig.2  | run_viscosity.py | Viscosity dependence (ν sweep) |
| Fig.3  | run_shell_baseline.py | Shell-resolved R(k,t) heatmap |
| Fig.4  | run_shell_lowvis.py | Low-ν long-time R(k,t) + cascade front |
| Fig.5  | run_matched_energy.py | Dissipation pre-payment effect |
| Fig.6  | run_abc.py | Geometry effect: TG vs ABC |
