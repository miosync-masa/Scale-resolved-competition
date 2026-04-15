import NSBarrier.NSWeakToStrongGap
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace NSLimitClosureStability

open NSGalerkinUniformEstimates
open NSGalerkinCompactnessActual
open NSWeakToStrongGap
open Filter

/-
  Purpose:
  prove that the closure step inequality is stable
  under subsequential convergence.

  If each Galerkin truncation in the extracted subsequence
  satisfies E_i(N0+(m+1)) - E_i(N0+m) ≤ M*C * E_i(N0+m),
  and the corresponding values converge pointwise to Elim,
  then the same step inequality holds for the limit
  trajectory Elim.
-/

-- ============================================================
-- SECTION 1: STABILITY DATA
-- ============================================================

/-- Limit closure stability data: a compactness extraction
where each family member satisfies the step inequality
and the subsequence converges pointwise to the limit. -/
structure LimitClosureStabilityData where
  compactnessData : GalerkinCompactnessData
  M : ℝ
  C : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hstep_family : ∀ i : ℕ, ∀ m : ℕ,
    compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + (m + 1))
      - compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + m)
      ≤ M * C * compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + m)
  hElim_tendsto : ∀ m : ℕ,
    Filter.Tendsto
      (fun j : ℕ => compactnessData.gronwallData.E
        (compactnessData.subseq j)
        (compactnessData.gronwallData.N0 + m))
      Filter.atTop
      (nhds (compactnessData.Elim
        (compactnessData.gronwallData.N0 + m)))
  /-- Pointwise convergence of the low-shell dissipation. -/
  hDlim_tendsto : ∀ m : ℕ,
    Filter.Tendsto
      (fun j : ℕ => compactnessData.Dlow
        (compactnessData.subseq j)
        (compactnessData.gronwallData.N0 + m))
      Filter.atTop
      (nhds (compactnessData.Dlim
        (compactnessData.gronwallData.N0 + m)))
  /-- Each family member satisfies Dlow ≤ C * E. -/
  hDlow_le_CE : ∀ i : ℕ, ∀ m : ℕ,
    compactnessData.Dlow i
        (compactnessData.gronwallData.N0 + m)
      ≤ C * compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + m)

#check @LimitClosureStabilityData

-- ============================================================
-- SECTION 2: STEP INEQUALITY PASSES TO THE LIMIT
-- ============================================================

/-- The closure step inequality passes to the limit
via closedness of the half-space {(a,b) | a ≤ b}
under pointwise convergence. -/
theorem hstep_limit_of_tendsto
    (d : LimitClosureStabilityData) :
    ∀ m : ℕ,
      d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + (m + 1))
        - d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + m)
        ≤ d.M * d.C
          * d.compactnessData.Elim
            (d.compactnessData.gronwallData.N0 + m) := by
  intro m
  let N0 := d.compactnessData.gronwallData.N0
  let E := d.compactnessData.gronwallData.E
  let sub := d.compactnessData.subseq
  let Elim := d.compactnessData.Elim
  have htendsto_m := d.hElim_tendsto m
  have htendsto_m1 := d.hElim_tendsto (m + 1)
  have hlhs : Filter.Tendsto
      (fun j => E (sub j) (N0 + (m + 1)) - E (sub j) (N0 + m))
      Filter.atTop (nhds (Elim (N0 + (m + 1)) - Elim (N0 + m))) :=
    Filter.Tendsto.sub htendsto_m1 htendsto_m
  have hrhs : Filter.Tendsto
      (fun j => d.M * d.C * E (sub j) (N0 + m))
      Filter.atTop (nhds (d.M * d.C * Elim (N0 + m))) :=
    htendsto_m.const_mul (d.M * d.C)
  -- Pass the inequality to the limit via le_of_tendsto_of_tendsto
  exact le_of_tendsto_of_tendsto hlhs hrhs
    (Filter.Eventually.of_forall (fun j => d.hstep_family (sub j) m))

#check @hstep_limit_of_tendsto

-- ============================================================
-- SECTION 2b: DISSIPATION CONTROL PASSES TO THE LIMIT
-- ============================================================

/-- The limit dissipation control Dlim ≤ C * Elim passes
to the limit by the same closed-set argument. -/
theorem hDlim_limit_of_tendsto
    (d : LimitClosureStabilityData) :
    ∀ m : ℕ,
      d.compactnessData.Dlim
          (d.compactnessData.gronwallData.N0 + m)
        ≤ d.C
          * d.compactnessData.Elim
            (d.compactnessData.gronwallData.N0 + m) := by
  intro m
  let N0 := d.compactnessData.gronwallData.N0
  let E := d.compactnessData.gronwallData.E
  let sub := d.compactnessData.subseq
  have hDtendsto := d.hDlim_tendsto m
  have hEtendsto := d.hElim_tendsto m
  have hrhs : Filter.Tendsto
      (fun j => d.C * E (sub j) (N0 + m))
      Filter.atTop
      (nhds (d.C * d.compactnessData.Elim (N0 + m))) :=
    hEtendsto.const_mul d.C
  exact le_of_tendsto_of_tendsto hDtendsto hrhs
    (Filter.Eventually.of_forall
      (fun j => d.hDlow_le_CE (sub j) m))

#check @hDlim_limit_of_tendsto

-- ============================================================
-- SECTION 3: BRIDGE TO NSWeakToStrongGap
-- ============================================================

/-- Build the weak-to-strong bridge from stability data. -/
noncomputable def toWeakToStrongCompactnessBridge
    (d : LimitClosureStabilityData) :
    WeakToStrongCompactnessBridge where
  compactnessData := d.compactnessData
  M := d.M
  C := d.C
  hM := d.hM
  hMC := d.hMC
  hstep_limit := hstep_limit_of_tendsto d
  hDlim := hDlim_limit_of_tendsto d

#check @toWeakToStrongCompactnessBridge

-- ============================================================
-- SECTION 4: MASTER THEOREMS
-- ============================================================

/-- **Limit Closure Stability Master Theorem.**

If each Galerkin truncation satisfies the step inequality
and the extracted subsequence converges pointwise to the
limit trajectory, then the limit satisfies the discrete
Gronwall bound. -/
theorem limit_closure_stability_master
    (d : LimitClosureStabilityData) :
    ∀ m : ℕ,
      d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + m)
        ≤ (1 + d.M * d.C) ^ m
          * d.compactnessData.Elim
            d.compactnessData.gronwallData.N0 :=
  weak_to_strong_gap_master
    (toWeakToStrongCompactnessBridge d)

#check @limit_closure_stability_master

end NSLimitClosureStability
