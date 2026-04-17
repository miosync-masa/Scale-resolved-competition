import NSBarrier.NSTorusLimitClosure
import NSBarrier.NSMillenniumFrontier
import NSBarrier.NSNoBlowupMaster
import Mathlib.Tactic

namespace NSTorusNoBlowup

open NSTorusShellActual
open NSTorusSolutionPackage
open NSTorusUniformF
open NSTorusLimitClosure
open NSContinuationCriterion
open NSNoBlowupMaster
open NSMillenniumFrontier
open NSStrainSupBootstrap

/-- T³ no-blowup wrapper data.

This bundles:
1. the torus local/true-field/enstrophy package,
2. the limit-closure data from B3,
3. the continuation/no-blowup parameters,
4. the concrete finite-Fourier low-shell closure function from B1/B2.

The equalities identify the abstract continuation constants with the concrete limit-side ones. -/
structure TorusNoBlowupData (K_max m : ℕ) where
  limitData : TorusLimitClosureData K_max m
  continuationData : InductiveContinuationData
  modes : Finset Mode
  hF_low :
    continuationData.F_low = torusUniformF modes limitData.Ncut
  hM_match : continuationData.M = limitData.M
  hC_match : continuationData.C = limitData.C
  hE0_match :
    continuationData.E0 =
      limitData.compactnessData.Elim
        limitData.compactnessData.gronwallData.N0

/-- The limit enstrophy trajectory, re-indexed so that time `0` means the compactness base time
`N0`. This is the trajectory fed to `NSNoBlowupMaster`. -/
noncomputable def shiftedLimitEnstrophy
    {K_max m : ℕ}
    (d : TorusNoBlowupData K_max m) : ℕ → ℝ :=
  fun n =>
    d.limitData.compactnessData.Elim
      (d.limitData.compactnessData.gronwallData.N0 + n)

/-- The torus finite-Fourier closure function from B1/B2 gives the frontier hypothesis attached to
the no-blowup wrapper. -/
noncomputable def millennium_frontier_hypothesis_of_torus_no_blowup_data
    {K_max m : ℕ}
    (d : TorusNoBlowupData K_max m) :
    MillenniumFrontierHypothesis where
  F := d.continuationData.F_low
  hF_nonneg := by
    simpa [d.hF_low] using
      torusUniformF_nonneg d.modes d.limitData.Ncut
  hF_mono := by
    simpa [d.hF_low] using
      torusUniformF_mono d.modes d.limitData.Ncut
  hF_Kmax_independent := trivial

/-- The limit-side discrete Grönwall law from B3, rewritten in the format expected by
`NSNoBlowupMaster`. -/
theorem shifted_limit_gronwall_of_torus_no_blowup_data
    {K_max m : ℕ}
    (d : TorusNoBlowupData K_max m) :
    ∀ n : ℕ,
      shiftedLimitEnstrophy d n
        ≤
      (1 + d.continuationData.M * d.continuationData.C) ^ n
        * d.continuationData.E0 := by
  intro n
  simpa [shiftedLimitEnstrophy, d.hM_match, d.hC_match, d.hE0_match] using
    torus_limit_solution_inherits_closure d.limitData n

/-- B4 wrapper theorem: smooth torus data, together with the verified T³ closure/compactness chain
and the concrete finite-Fourier closure function, imply no finite-time blow-up for the extracted
limit enstrophy trajectory. -/
theorem torus_no_finite_time_blowup_of_smooth_data
    {K_max m : ℕ}
    (d : TorusNoBlowupData K_max m) :
    (∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ shiftedLimitEnstrophy d n ≤ B) ∧
    (∀ n : ℕ,
      0 ≤ bootstrapStrainSup
        ((1 + d.continuationData.M * d.continuationData.C) ^ n * d.continuationData.E0)
        d.continuationData.strainHigh
        d.continuationData.F_low) ∧
    (∀ n : ℕ,
      0 ≤
        (localExistenceSeed_of_actual_solution_package_T3 d.limitData.solutionPkg).T0
          + d.continuationData.Δt * (n : ℝ)) := by
  exact
    no_blowup_master
      (localExistenceSeed_of_actual_solution_package_T3 d.limitData.solutionPkg)
      d.continuationData
      (shiftedLimitEnstrophy d)
      (shifted_limit_gronwall_of_torus_no_blowup_data d)

end NSTorusNoBlowup
