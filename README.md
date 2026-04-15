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

## Lean 4 Formal Verification

The complete formal proof is located in the `/lean4/` directory.

### Quick Start

```bash
cd lean4/
lake build        # Full verification — 0 sorry, 0 axiom
```

### What is verified

| Item | Value |
|------|-------|
| Files | 119 |
| Lines | 22,181 |
| Theorems / Lemmas / Defs | 807 |
| `sorry` | **0** |
| `axiom` | **0** |
| Irreducible external assumption | **1** — `ω₀ ∈ L²(T³)` |
| Lean version | 4.x + Mathlib |

### Architecture

The proof consists of three master theorems connected by a single logical chain:

| Theorem | Statement | Layer |
|---------|-----------|-------|
| **Theorem I** (Closure) | Conditional Gronwall from triad geometry + finite Bernstein | Layer 12 |
| **Theorem II** (Realization) | True NS fields discharge Theorem I hypotheses via Galerkin ODE | Layer 12 |
| **Theorem III** (No-Blowup) | Bootstrap + continuation → no minimal blowup scenario | Layer 13 |
| **K_max Limit Passage** | Arzelà-Ascoli extraction → weak-to-strong gap on limit | Layer 14-15 |

All 807 statements are organized across 17 layers. See [`FULL_THEOREM_REGISTRY.md`](lean4/FULL_THEOREM_REGISTRY.md) for the complete list.

### Dependency Graph

The formal proof has 119 files with 274 inter-file dependencies. The layer-level architecture:

```
Layer 0  Abstract Barrier Core (k⁴ barrier, finite source reduction)
   ↓
Layer 1  Integrated hinc (enstrophy increment identity)
   ↓
Layer 2  Galerkin ODE Realization (product rule, FTC)
   ↓
Layer 3  Triad Geometry (offset C₀=2, support exclusion)
   ↓
Layer 4  Finite-Band Bernstein (Cauchy-Schwarz on finite modes)
   ↓
Layer 5  Shell-Block Modewise Decomposition
   ↓
Layer 6-7  Torus L²/L∞ Analysis → Strain Tensor
   ↓
Layer 8  True NS Fields [PDE input: ω₀ ∈ L²(T³)]
   ↓
Layer 9-10  Abstract Fourier Chain → Named Theorem Surface
   ↓
Layer 11  PDE Regularity & Galerkin Existence (Mathlib IsPicardLindelof)
   ↓
Layer 12  ★ Master Theorems (Closure + Realization + Main) ★
   ↓
Layer 13  Bootstrap / Continuation / No-Blowup Master
   ↓
Layer 14  Uniform Estimates & Compactness (Arzelà-Ascoli)
   ↓
Layer 15  K_max-Uniform Analysis (equicontinuity via MVT)
   ↓
Layer 16  Limit Passage → Weak-to-Strong Gap
   ↓
   ★ Millennium Frontier ★
```

### Irreducible PDE Frontier

After bootstrap regeneration, the **sole external assumption** is:

```
omega_mem : MemLp (omega k) 2    — initial vorticity ω₀ ∈ L²(T³)
```

All other assumptions previously appearing as external inputs have been internalized:

| Previously external | Now internal via |
|---|---|
| `Sop_ae_bound` | `bootstrapStrainSup` (regenerated at each step) |
| `sigma_ae_bound` | `sigma_bound_of_ae_bound` |
| `sigma_mem` | `NSActualSigmaBoundProof` |
| `stretch_mem` | `stretch_memLp_of_dominated_and_measurable` |
| Cauchy-Lipschitz | Mathlib `IsPicardLindelof` (sorry-free) |
| Arzelà-Ascoli | Mathlib `BoundedContinuousFunction.arzela_ascoli` (sorry-free) |

### Key Mathlib Connections (all sorry-free)

- `IsPicardLindelof` — ODE existence
- `BoundedContinuousFunction.arzela_ascoli` — compactness extraction
- `IsCompact.tendsto_subseq` — subsequence extraction
- `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` — MVT for Lipschitz
- `integral_eq_sub_of_hasDerivAt` — FTC for shellwise identity

### Reproducing

```bash
# Clone
git clone https://github.com/miosync-masa/Scale-resolved-competition.git
cd Scale-resolved-competition/lean4/

# Build (requires Lean 4 + elan)
lake update
lake build

# Expected output: Build completed successfully. (0 errors)
```

No `sorry`. No `axiom`. Every statement is machine-checked.

## License

MIT

## Citation

If you use this code, please cite the associated paper (submitted to JFM, 2026).
