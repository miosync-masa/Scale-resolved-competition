import NSBarrier.NSR3LimitClosure
import NSBarrier.NSR3MillenniumFrontier
import NSBarrier.NSNoBlowupMaster
import Mathlib.Tactic

namespace NSR3NoBlowup

open NSContinuationCriterion
open NSMillenniumFrontier
open NSNoBlowupMaster
open NSR3LimitClosure
open NSR3MillenniumFrontier
open NSR3SolutionPackage
open NSR3UniformF
open NSStrainSupBootstrap

/-- `R³` no-blowup wrapper data, parallel to the torus-side one. -/
structure R3NoBlowupData (K_max m : ℕ) where
  limitData : R3LimitClosureData K_max m
  continuationData : InductiveContinuationData
  hF_low :
    continuationData.F_low = r3UniformF limitData.Ncut
  hM_match : continuationData.M = limitData.M
  hC_match : continuationData.C = limitData.C
  hE0_match :
    continuationData.E0 =
      limitData.compactnessData.Elim
        limitData.compactnessData.gronwallData.N0

/-- The limit enstrophy trajectory, re-indexed so that time `0` means the
compactness base time `N0`. -/
noncomputable def shiftedLimitEnstrophy_R3
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) : ℕ → ℝ :=
  fun n =>
    d.limitData.compactnessData.Elim
      (d.limitData.compactnessData.gronwallData.N0 + n)

/-- The Euclidean finite-band closure function from A1/A2 gives the frontier
hypothesis attached to the no-blowup wrapper. -/
noncomputable def millennium_frontier_hypothesis_of_R3_no_blowup_data
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) :
    MillenniumFrontierHypothesis where
  F := d.continuationData.F_low
  hF_nonneg := by
    simpa [d.hF_low] using
      r3UniformF_nonneg d.limitData.Ncut
  hF_mono := by
    simpa [d.hF_low] using
      r3UniformF_mono d.limitData.Ncut
  hF_Kmax_independent := trivial

/-- The limit-side discrete Gronwall law from A3, rewritten in the format
expected by `NSNoBlowupMaster`. -/
theorem shifted_limit_gronwall_of_R3_no_blowup_data
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) :
    ∀ n : ℕ,
      shiftedLimitEnstrophy_R3 d n
        ≤
      (1 + d.continuationData.M * d.continuationData.C) ^ n
        * d.continuationData.E0 := by
  intro n
  simpa [shiftedLimitEnstrophy_R3, d.hM_match, d.hC_match, d.hE0_match] using
    R3_limit_solution_inherits_closure d.limitData n

/-- A4 wrapper theorem: smooth Euclidean data, together with the verified `R³`
closure/compactness chain and the concrete finite-band closure function, imply
no finite-time blow-up for the extracted limit enstrophy trajectory. -/
theorem R3_no_finite_time_blowup_of_smooth_data
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) :
    (∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ shiftedLimitEnstrophy_R3 d n ≤ B) ∧
    (∀ n : ℕ,
      0 ≤ bootstrapStrainSup
        ((1 + d.continuationData.M * d.continuationData.C) ^ n * d.continuationData.E0)
        d.continuationData.strainHigh
        d.continuationData.F_low) ∧
    (∀ n : ℕ,
      0 ≤
        (localExistenceSeed_of_actual_solution_package_R3 d.limitData.solutionPkg).T0
          + d.continuationData.Δt * (n : ℝ)) := by
  exact
    no_blowup_master
      (localExistenceSeed_of_actual_solution_package_R3 d.limitData.solutionPkg)
      d.continuationData
      (shiftedLimitEnstrophy_R3 d)
      (shifted_limit_gronwall_of_R3_no_blowup_data d)

end NSR3NoBlowup
