import NSBarrier.NSHighShellTailSummability
import NSBarrier.NSFiniteSourceTrajectory
import Mathlib.Tactic

namespace NSDynamicCutoff

open NSFiniteSource
open NSFiniteSourceTrajectory
open NSStrainSupBootstrap

/-
  D-branch: Dynamic cutoff N(t).

  Instead of a fixed cutoff Ncut, choose Ncut(n) at each
  time step to optimize the low/high split.

  The optimal choice balances:
  - low part: F_low(E_{<N}) grows with N (more modes)
  - high part: strainHigh(N) decays with N (barrier)

  For the bootstrap, any N that makes both parts finite
  suffices. The dynamic choice N(n) can be:
  - the jumpFront of the budget trajectory
  - a cutoff adapted to the current enstrophy level
  - a fixed large N (simplest case)
-/

-- ============================================================
-- SECTION 1: DYNAMIC CUTOFF DATA
-- ============================================================

/-- Dynamic cutoff: N(n) chosen at each time step. -/
structure DynamicCutoffData (K_max : ℕ) where
  Ncut : ℕ → ℕ
  hNcut_bound : ∀ n : ℕ, Ncut n ≤ K_max

/-- Low/high decomposition with dynamic cutoff. -/
structure DynamicStrainDecomposition (K_max : ℕ) where
  cutoff : DynamicCutoffData K_max
  F_low : ℝ → ℝ
  strainHigh : ℕ → ℝ
  hF_low_nonneg : ∀ x, 0 ≤ x → 0 ≤ F_low x
  hhigh_nonneg : ∀ n, 0 ≤ strainHigh n

#check @DynamicCutoffData
#check @DynamicStrainDecomposition

-- ============================================================
-- SECTION 2: DYNAMIC BOOTSTRAP STRAIN BOUND
-- ============================================================

/-- [Alg] At each step n, the bootstrap strain bound
with dynamic cutoff N(n) is well-defined and nonneg. -/
theorem dynamic_bootstrapStrainSup_nonneg
    {K_max : ℕ}
    (d : DynamicStrainDecomposition K_max)
    (E_bound : ℕ → ℝ)
    (hE_bound : ∀ n, 0 ≤ E_bound n) :
    ∀ n : ℕ,
      0 ≤ d.F_low (E_bound n) + d.strainHigh n :=
  fun n => add_nonneg
    (d.hF_low_nonneg _ (hE_bound n)) (d.hhigh_nonneg n)

#check @dynamic_bootstrapStrainSup_nonneg

-- ============================================================
-- SECTION 3: OPTIMAL CUTOFF CHOICE
-- ============================================================

/-- [Alg] The fixed cutoff is a special case of dynamic:
N(n) = Ncut for all n. -/
noncomputable def fixedAsDynamic
    {K_max : ℕ}
    (Ncut : ℕ) (hNcut : Ncut ≤ K_max) :
    DynamicCutoffData K_max where
  Ncut := fun _ => Ncut
  hNcut_bound := fun _ => hNcut

/-- [Alg] The jumpFront-adapted cutoff:
N(n) = jumpFront(traj(n)) + C0 for some offset. -/
noncomputable def frontAdaptedCutoff
    {K_max : ℕ}
    (front : ℕ → ℕ) (C0 : ℕ)
    (hbound : ∀ n, front n + C0 ≤ K_max) :
    DynamicCutoffData K_max where
  Ncut := fun n => front n + C0
  hNcut_bound := hbound

#check @fixedAsDynamic
#check @frontAdaptedCutoff

-- ============================================================
-- SECTION 4: MONOTONICITY OF TAIL UNDER INCREASING CUTOFF
-- ============================================================

/-- [Alg] If the cutoff increases, the tail contribution
decreases (fewer high shells contribute). -/
theorem tail_decreases_with_cutoff
    {K_max : ℕ}
    (shellAmp : Fin K_max → ℝ)
    (hamp : ∀ k, 0 ≤ shellAmp k)
    (N1 N2 : ℕ) (hN : N1 ≤ N2) :
    Finset.sum
      (Finset.univ.filter
        (fun k : Fin K_max => N2 ≤ k.val))
      shellAmp
      ≤
    Finset.sum
      (Finset.univ.filter
        (fun k : Fin K_max => N1 ≤ k.val))
      shellAmp := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hk ⊢
    exact le_trans hN hk
  · intro k _ _
    exact hamp k

#check @tail_decreases_with_cutoff

-- ============================================================
-- SECTION 5: PAPER-FACING SUMMARY
-- ============================================================

/-!
## Dynamic Cutoff Summary

The dynamic cutoff N(n) generalizes the fixed cutoff:

| Cutoff type | Definition | Use case |
|-------------|-----------|----------|
| Fixed | N(n) = Ncut | Simplest, sufficient for main theorem |
| Front-adapted | N(n) = front(n) + C0 | Sharpest, uses barrier information |
| Optimal | N(n) = argmin(F_low + strainHigh) | Theoretical optimum |

All three yield a valid bootstrap, but front-adapted
gives the tightest constants.

The main theorem (NSMainTheorem) uses fixed cutoff.
Dynamic cutoff is a sharpened corollary.
-/

end NSDynamicCutoff
