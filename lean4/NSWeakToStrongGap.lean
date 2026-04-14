import NSBarrier.NSGalerkinCompactnessActual
import NSBarrier.NSFiniteSourceConditionalGronwall
import Mathlib.Tactic

namespace NSWeakToStrongGap

open NSGalerkinUniformEstimates
open NSGalerkinCompactnessActual
open NSFiniteSourceConditionalGronwall

/-
  Purpose: isolate the exact hypotheses under which a
  compactness limit inherits the closure theorem and hence
  satisfies the same eventual discrete Gronwall bound.

  This file does NOT solve compactness by itself.
  It makes the weak-to-strong frontier explicit.
-/

-- ============================================================
-- SECTION 1: LIMIT-SIDE CLOSURE DATA
-- ============================================================

/-- Limit-side closure data.

The key question is whether the closure hypotheses survive
to the limit object. The single critical hypothesis is
`hstep`: the limit enstrophy satisfies the same one-step
growth inequality as the Galerkin family members. -/
structure WeakToStrongGapData where
  Elim : ℕ → ℝ
  Dlim : ℕ → ℝ
  M : ℝ
  C : ℝ
  N0 : ℕ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hstep : ∀ m : ℕ,
    Elim (N0 + (m + 1)) - Elim (N0 + m)
      ≤ M * C * Elim (N0 + m)
  hDlim : ∀ m : ℕ,
    Dlim (N0 + m) ≤ C * Elim (N0 + m)

#check @WeakToStrongGapData

-- ============================================================
-- SECTION 2: LIMIT-SIDE DISCRETE GRONWALL
-- ============================================================

/-- If the limit enstrophy satisfies the one-step growth
inequality, then it satisfies the full discrete Gronwall
bound by induction. -/
theorem discrete_gronwall_on_limit
    (d : WeakToStrongGapData) :
    ∀ m : ℕ,
      d.Elim (d.N0 + m)
        ≤ (1 + d.M * d.C) ^ m * d.Elim d.N0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep' :
        d.Elim (d.N0 + (m + 1))
          ≤ (1 + d.M * d.C) * d.Elim (d.N0 + m) := by
      have := d.hstep m
      nlinarith
    calc d.Elim (d.N0 + (m + 1))
        ≤ (1 + d.M * d.C) * d.Elim (d.N0 + m) :=
          hstep'
      _ ≤ (1 + d.M * d.C)
            * ((1 + d.M * d.C) ^ m * d.Elim d.N0) := by
          exact mul_le_mul_of_nonneg_left ih
            (by linarith [d.hMC])
      _ = (1 + d.M * d.C) ^ (m + 1) * d.Elim d.N0 := by
          ring

#check @discrete_gronwall_on_limit

-- ============================================================
-- SECTION 3: COMPACTNESS + STABILITY => LIMIT CLOSURE
-- ============================================================

/-- Compactness extraction together with closure-stability
hypotheses produces a limit-side closure theorem. -/
structure WeakToStrongCompactnessBridge where
  compactnessData : GalerkinCompactnessData
  M : ℝ
  C : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hstep_limit : ∀ m : ℕ,
    compactnessData.Elim
        (compactnessData.gronwallData.N0 + (m + 1))
      - compactnessData.Elim
        (compactnessData.gronwallData.N0 + m)
      ≤ M * C * compactnessData.Elim
        (compactnessData.gronwallData.N0 + m)
  hDlim : ∀ m : ℕ,
    compactnessData.Dlim
        (compactnessData.gronwallData.N0 + m)
      ≤ C * compactnessData.Elim
        (compactnessData.gronwallData.N0 + m)

#check @WeakToStrongCompactnessBridge

noncomputable def toWeakToStrongGapData
    (d : WeakToStrongCompactnessBridge) :
    WeakToStrongGapData where
  Elim := d.compactnessData.Elim
  Dlim := d.compactnessData.Dlim
  M := d.M
  C := d.C
  N0 := d.compactnessData.gronwallData.N0
  hM := d.hM
  hMC := d.hMC
  hstep := d.hstep_limit
  hDlim := d.hDlim

theorem eventual_discrete_gronwall_on_limit
    (d : WeakToStrongCompactnessBridge) :
    ∀ m : ℕ,
      d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + m)
        ≤ (1 + d.M * d.C) ^ m
          * d.compactnessData.Elim
            d.compactnessData.gronwallData.N0 :=
  discrete_gronwall_on_limit (toWeakToStrongGapData d)

#check @eventual_discrete_gronwall_on_limit

-- ============================================================
-- SECTION 4: PAPER-FACING MASTER THEOREM
-- ============================================================

/-- **Weak-to-Strong Gap Master Theorem.**

If the compactness limit inherits the closure step
inequality, then it satisfies the same eventual discrete
Gronwall law as the Galerkin family.

The remaining question — whether `hstep_limit` holds —
is the **weak-to-strong gap**: the single condition that
separates a weak compactness limit from a strong enough
limit for the barrier argument. -/
theorem weak_to_strong_gap_master
    (d : WeakToStrongCompactnessBridge) :
    ∀ m : ℕ,
      d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + m)
        ≤ (1 + d.M * d.C) ^ m
          * d.compactnessData.Elim
            d.compactnessData.gronwallData.N0 :=
  eventual_discrete_gronwall_on_limit d

#check @weak_to_strong_gap_master

end NSWeakToStrongGap
