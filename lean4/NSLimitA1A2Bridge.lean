import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import NSBarrier.NSAnalyticA2
import NSBarrier.NSAnalyticA2Bridge
import NSBarrier.NSUniformA2Bridge
import NSBarrier.NSUniformA1Bridge
import NSBarrier.NSLimit
import NSBarrier.NSLimitA2Bridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSUniformBridge
open NSAnalyticA2
open NSAnalyticA2Bridge
open NSUniformA2Bridge
open NSUniformA1Bridge
open NSLimit
open NSLimitA2Bridge

namespace NSLimitA1A2Bridge

-- ============================================================
-- SECTION 1: A1+A2 -> UNIFORM EVENTUAL BOUND
-- ============================================================

/-- Combined A1+A2 hypotheses imply a uniform eventual front bound,
    provided one can extract a uniform seed bound at the common nonincrease threshold. -/
theorem uniform_eventually_bounded_from_locality_A1A2_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    UniformEventuallyBoundedFront btraj := by
  rcases
    uniform_eventually_nonincreasing_front_from_locality_A1A2_inst
      btraj ftraj Gfam rtraj ν C_str C_shell
      hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD with
    ⟨N, hN⟩
  rcases hseed N hN with ⟨M, hM⟩
  exact uniform_eventually_bounded_of_threshold_seed btraj N M hN hM

/-- Unit-shell specialization of the previous theorem. -/
theorem uniform_eventually_bounded_from_locality_A1A2_unit_shell_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ν C_str : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * (9 / 4 : ℝ)))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    UniformEventuallyBoundedFront btraj := by
  exact
    uniform_eventually_bounded_from_locality_A1A2_with_seed
      btraj ftraj Gfam unitShellRadiusSqTrajectory ν C_str (9 / 4 : ℝ)
      hCstr hS hXi hE hA hloc hgc h0 hXiR uniform_unitShellRadiusSq_control hD hseed

#check @uniform_eventually_bounded_from_locality_A1A2_with_seed
#check @uniform_eventually_bounded_from_locality_A1A2_unit_shell_with_seed

-- ============================================================
-- SECTION 2: A1+A2 -> TRUNCATION LIMIT EXISTENCE
-- ============================================================

/-- Combined A1+A2 hypotheses plus truncation consistency imply eventual
    existence of the truncation-limit front. -/
theorem eventual_truncation_limit_exists_from_locality_A1A2_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hcons : ConsistentTruncation btraj)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    EventualTruncationLimitExists btraj := by
  have hbound : UniformEventuallyBoundedFront btraj :=
    uniform_eventually_bounded_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  exact
    NSLimit.eventual_truncation_limit_exists_of_uniform_bound
      btraj hcons hbound

/-- Unit-shell specialization of the previous theorem. -/
theorem eventual_truncation_limit_exists_from_locality_A1A2_unit_shell_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ν C_str : ℝ)
    (hcons : ConsistentTruncation btraj)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * (9 / 4 : ℝ)))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    EventualTruncationLimitExists btraj := by
  exact
    eventual_truncation_limit_exists_from_locality_A1A2_with_seed
      btraj ftraj Gfam unitShellRadiusSqTrajectory ν C_str (9 / 4 : ℝ)
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR uniform_unitShellRadiusSq_control hD hseed

#check @eventual_truncation_limit_exists_from_locality_A1A2_with_seed
#check @eventual_truncation_limit_exists_from_locality_A1A2_unit_shell_with_seed

-- ============================================================
-- SECTION 3: POINTWISE CONSEQUENCES
-- ============================================================

/-- Combined A1+A2 hypotheses imply pointwise eventual front boundedness
    for each truncation level. -/
theorem pointwise_eventually_bounded_from_locality_A1A2_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  have hbound : UniformEventuallyBoundedFront btraj :=
    uniform_eventually_bounded_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  exact
    pointwise_eventual_bound_of_uniform_eventual_bound
      btraj hbound

#check @pointwise_eventually_bounded_from_locality_A1A2_with_seed

end NSLimitA1A2Bridge
