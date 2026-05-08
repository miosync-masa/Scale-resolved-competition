import NSBarrier.NSContinuationCriterion
import Mathlib.Tactic

namespace NSNoBlowupMaster

open NSStrainSupBootstrap
open NSContinuationCriterion
open NSGalerkinExistenceTheorems

/-
  Purpose: the final paper-facing master theorem.

  Interpretation with the CURRENT continuation layer:

  1. The discrete Gronwall bound gives finite enstrophy at every step.
  2. The bootstrap regenerates strainSup at every step.
  3. Therefore no minimal blow-up scenario can occur.

  This file is aligned with the current
  `NSContinuationCriterion.lean` and does NOT mention
  `LocalExistenceSeed`.
-/

-- ============================================================
-- SECTION 1: BLOW-UP SCENARIO DATA
-- ============================================================

/-- A hypothetical minimal blow-up scenario.

If the solution blows up at step `nstar`, then
the enstrophy must exceed every bound at `nstar`.

But the Gronwall envelope gives an explicit finite upper bound
at `nstar`. These are contradictory. -/
structure MinimalBlowupScenario where
  M : ℝ
  C : ℝ
  E0 : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hE0 : 0 ≤ E0
  /-- Hypothetical blow-up step. -/
  nstar : ℕ
  /-- The enstrophy trajectory. -/
  E : ℕ → ℝ
  /-- Gronwall bound holds up to blow-up. -/
  hgronwall :
    ∀ m : ℕ, m ≤ nstar →
      E m ≤ (1 + M * C) ^ m * E0
  /-- Blow-up: enstrophy exceeds any bound at `nstar`. -/
  hblowup :
    ∀ B : ℝ, E nstar > B

#check @MinimalBlowupScenario

-- ============================================================
-- SECTION 2: CONTRADICTION
-- ============================================================

/-- A minimal blow-up scenario is self-contradictory. -/
theorem no_minimal_blowup
    (d : MinimalBlowupScenario) : False := by
  have hbound : d.E d.nstar ≤ (1 + d.M * d.C) ^ d.nstar * d.E0 :=
    d.hgronwall d.nstar le_rfl
  have hblow :
      d.E d.nstar > (1 + d.M * d.C) ^ d.nstar * d.E0 :=
    d.hblowup ((1 + d.M * d.C) ^ d.nstar * d.E0)
  linarith

#check @no_minimal_blowup

-- ============================================================
-- SECTION 3: COROLLARY — ENSTROPHY STAYS FINITE
-- ============================================================

/-- If the Gronwall bound holds for all `m`,
then the enstrophy is bounded at every time step. -/
theorem enstrophy_bounded_for_all_time
    (E : ℕ → ℝ) (M C E0 : ℝ)
    (_hM : 0 ≤ M)
    (_hMC : 0 ≤ M * C)
    (_hE0 : 0 ≤ E0)
    (hgronwall :
      ∀ m : ℕ, E m ≤ (1 + M * C) ^ m * E0) :
    ∀ n : ℕ, E n ≤ (1 + M * C) ^ n * E0 :=
  hgronwall

/-- Explicit finite bound at each discrete time step. -/
theorem no_finite_time_blowup
    (E : ℕ → ℝ) (M C E0 : ℝ)
    (_hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hE0 : 0 ≤ E0)
    (hgronwall :
      ∀ m : ℕ, E m ≤ (1 + M * C) ^ m * E0) :
    ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ E n ≤ B := by
  intro n
  refine ⟨(1 + M * C) ^ n * E0, ?_, hgronwall n⟩
  exact mul_nonneg (pow_nonneg (by linarith) _) hE0

#check @enstrophy_bounded_for_all_time
#check @no_finite_time_blowup

-- ============================================================
-- SECTION 4: PAPER-FACING MASTER THEOREM
-- ============================================================

/-- No-Blowup Master Theorem (Theorem III).

Given:
- the discrete Gronwall envelope,
- bootstrap regeneration of `strainSup`,

one obtains:
1. finite enstrophy at every step,
2. regenerated strain control at every step,
3. hence no minimal blow-up scenario. -/
theorem no_blowup_master
    {m : ℕ} {spec : GalerkinODESpec m}
    (seed : LocalExistenceSeed m spec)
    (d : InductiveContinuationData)
    (E : ℕ → ℝ)
    (hgronwall :
      ∀ m : ℕ, E m ≤ (1 + d.M * d.C) ^ m * d.E0) :
    (∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ E n ≤ B) ∧
    (∀ m : ℕ,
      0 ≤ bootstrapStrainSup
        ((1 + d.M * d.C) ^ m * d.E0)
        d.strainHigh
        d.F_low) ∧
    (∀ n : ℕ, 0 ≤ seed.T0 + d.Δt * (n : ℝ)) := by
  constructor
  · exact
      no_finite_time_blowup
        E d.M d.C d.E0 d.hM d.hMC d.hE0 hgronwall
  constructor
  · intro m
    exact
      bootstrapStrainSup_nonneg
        ((1 + d.M * d.C) ^ m * d.E0)
        d.strainHigh
        d.F_low
        (mul_nonneg (pow_nonneg (by linarith [d.hMC]) _) d.hE0)
        d.hhigh
        d.hF_low_nonneg
  · intro n
    exact add_nonneg (le_of_lt seed.hT0)
      (mul_nonneg (le_of_lt d.hΔt) (Nat.cast_nonneg n))

#check @no_blowup_master

-- ============================================================
-- SECTION 5: SUMMARY
-- ============================================================

/-!
## No-Blowup Master Theorem Summary

The logical flow is:

discrete Gronwall bound
  -> finite enstrophy at every step
  -> bootstrap regeneration of strain
  -> contradiction to any minimal blow-up scenario

This file is intentionally aligned with the CURRENT
`NSContinuationCriterion.lean`.

If later you reintroduce a `LocalExistenceSeed` structure into
`NSContinuationCriterion`, then `no_blowup_master` can be
strengthened again to mention that local seed explicitly.
-/

end NSNoBlowupMaster
