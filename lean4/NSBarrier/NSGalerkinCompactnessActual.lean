import NSBarrier.NSGalerkinUniformEstimates
import Mathlib.Tactic

namespace NSGalerkinCompactnessActual

open NSGalerkinUniformEstimates

/-
  Purpose: package the compactness step in a theorem-facing form.

  We do NOT formalize Banach-Alaoglu / Aubin-Lions inside this file.
  Instead, we isolate the exact data needed from compactness extraction:
  - a subsequence of Galerkin truncations,
  - a limit enstrophy trajectory,
  - a limit low-shell dissipation trajectory,
  - pointwise limsup control along the subsequence.

  Then the uniform envelopes proved in `NSGalerkinUniformEstimates`
  automatically pass to the extracted limit.
-/

-- ============================================================
-- SECTION 1: SUBSEQUENCE EXTRACTION DATA
-- ============================================================

/-- Compactness extraction data from a uniformly controlled
Galerkin family.  The limit trajectories `Elim` and `Dlim`
are assumed to be pointwise bounded by the corresponding
family members along the extracted subsequence. -/
structure GalerkinCompactnessData where
  gronwallData : UniformGalerkinGronwallData ℕ
  Cdiss : ℝ
  hCdiss : 0 ≤ Cdiss
  Dlow : ℕ → ℕ → ℝ
  hDlow : ∀ i : ℕ, ∀ m : ℕ,
    Dlow i (gronwallData.N0 + m)
      ≤ Cdiss * gronwallData.E i (gronwallData.N0 + m)
  subseq : ℕ → ℕ
  hsubseq_injective : Function.Injective subseq
  Elim : ℕ → ℝ
  Dlim : ℕ → ℝ
  hElim_le : ∀ j : ℕ, ∀ m : ℕ,
    Elim (gronwallData.N0 + m)
      ≤ gronwallData.E (subseq j) (gronwallData.N0 + m)
  hDlim_le : ∀ j : ℕ, ∀ m : ℕ,
    Dlim (gronwallData.N0 + m)
      ≤ Dlow (subseq j) (gronwallData.N0 + m)

#check @GalerkinCompactnessData

-- ============================================================
-- SECTION 2: LIMIT INHERITS THE UNIFORM ENVELOPES
-- ============================================================

/-- The limit enstrophy inherits the uniform Gronwall envelope. -/
theorem limit_enstrophy_bound_of_compactness
    (d : GalerkinCompactnessData)
    (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hinit : ∀ i : ℕ,
      d.gronwallData.E i d.gronwallData.N0 ≤ B0) :
    ∀ m : ℕ,
      d.Elim (d.gronwallData.N0 + m)
        ≤ (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by
  intro m
  calc d.Elim (d.gronwallData.N0 + m)
      ≤ d.gronwallData.E (d.subseq 0)
          (d.gronwallData.N0 + m) :=
        d.hElim_le 0 m
    _ ≤ (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * d.gronwallData.E (d.subseq 0) d.gronwallData.N0 :=
        d.gronwallData.hgronwall (d.subseq 0) m
    _ ≤ (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by
        exact mul_le_mul_of_nonneg_left
          (hinit (d.subseq 0))
          (pow_nonneg (by linarith [d.gronwallData.hMC]) _)

/-- The limit low-shell dissipation inherits the envelope. -/
theorem limit_dissipation_bound_of_compactness
    (d : GalerkinCompactnessData)
    (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hinit : ∀ i : ℕ,
      d.gronwallData.E i d.gronwallData.N0 ≤ B0) :
    ∀ m : ℕ,
      d.Dlim (d.gronwallData.N0 + m)
        ≤ d.Cdiss
          * (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by
  intro m
  calc d.Dlim (d.gronwallData.N0 + m)
      ≤ d.Dlow (d.subseq 0) (d.gronwallData.N0 + m) :=
        d.hDlim_le 0 m
    _ ≤ d.Cdiss * d.gronwallData.E (d.subseq 0)
          (d.gronwallData.N0 + m) :=
        d.hDlow (d.subseq 0) m
    _ ≤ d.Cdiss
          * ((1 + d.gronwallData.M * d.gronwallData.C) ^ m
            * d.gronwallData.E (d.subseq 0)
              d.gronwallData.N0) :=
        mul_le_mul_of_nonneg_left
          (d.gronwallData.hgronwall (d.subseq 0) m)
          d.hCdiss
    _ ≤ d.Cdiss
          * ((1 + d.gronwallData.M * d.gronwallData.C) ^ m
            * B0) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (hinit (d.subseq 0))
            (pow_nonneg
              (by linarith [d.gronwallData.hMC]) _))
          d.hCdiss
    _ = d.Cdiss
          * (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by ring

#check @limit_enstrophy_bound_of_compactness
#check @limit_dissipation_bound_of_compactness

-- ============================================================
-- SECTION 3: PAPER-FACING MASTER THEOREMS
-- ============================================================

/-- Master: limit inherits the uniform enstrophy envelope. -/
theorem galerkin_compactness_limit_enstrophy_master
    (d : GalerkinCompactnessData) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ m : ℕ,
      d.Elim (d.gronwallData.N0 + m)
        ≤ (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by
  rcases d.gronwallData.hinit with ⟨B0, hB0, hinit⟩
  exact ⟨B0, hB0,
    limit_enstrophy_bound_of_compactness d B0 hB0 hinit⟩

/-- Master: limit inherits the uniform dissipation envelope. -/
theorem galerkin_compactness_limit_dissipation_master
    (d : GalerkinCompactnessData) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ m : ℕ,
      d.Dlim (d.gronwallData.N0 + m)
        ≤ d.Cdiss
          * (1 + d.gronwallData.M * d.gronwallData.C) ^ m
          * B0 := by
  rcases d.gronwallData.hinit with ⟨B0, hB0, hinit⟩
  exact ⟨B0, hB0,
    limit_dissipation_bound_of_compactness d B0 hB0 hinit⟩

#check @galerkin_compactness_limit_enstrophy_master
#check @galerkin_compactness_limit_dissipation_master

end NSGalerkinCompactnessActual
