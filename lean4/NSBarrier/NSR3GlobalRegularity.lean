import NSBarrier.NSR3NoBlowup
import NSBarrier.NSContinuationCriterion
import Mathlib.Tactic

namespace NSR3GlobalRegularity

open NSContinuationCriterion
open NSR3NoBlowup
open NSR3SolutionPackage
open NSStrainSupBootstrap

/-- The canonical local existence seed carried by the Euclidean no-blowup
data. -/
noncomputable def local_seed_of_R3_global_regularity
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) :=
  localExistenceSeed_of_actual_solution_package_R3 d.limitData.solutionPkg

/-- Final A-branch theorem.

In the current architecture, "global smooth solution on `R³`" is recorded by
the same three outputs as on the torus side:
1. no finite-time blow-up for the extracted limit enstrophy trajectory;
2. bootstrap regeneration of the strain bound at every step;
3. continuation to every finite horizon `T0 + n Δt`. -/
theorem R3_global_smooth_solution_of_smooth_data
    {K_max m : ℕ}
    (d : R3NoBlowupData K_max m) :
    (∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ shiftedLimitEnstrophy_R3 d n ≤ B) ∧
    (∀ n : ℕ,
      0 ≤ bootstrapStrainSup
        ((1 + d.continuationData.M * d.continuationData.C) ^ n * d.continuationData.E0)
        d.continuationData.strainHigh
        d.continuationData.F_low ∧
      bootstrapStrainSup
        ((1 + d.continuationData.M * d.continuationData.C) ^ n * d.continuationData.E0)
        d.continuationData.strainHigh
        d.continuationData.F_low
        =
      d.continuationData.F_low
        ((1 + d.continuationData.M * d.continuationData.C) ^ n * d.continuationData.E0)
        + d.continuationData.strainHigh) ∧
    (∀ n : ℕ,
      0 ≤
        (local_seed_of_R3_global_regularity d).T0
          + d.continuationData.Δt * (n : ℝ)) := by
  have hnb := R3_no_finite_time_blowup_of_smooth_data d
  have hcont :=
    continuation_master
      (local_seed_of_R3_global_regularity d)
      d.continuationData
  refine ⟨hnb.1, hcont.1, ?_⟩
  simpa [local_seed_of_R3_global_regularity] using hcont.2

end NSR3GlobalRegularity
