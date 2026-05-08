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
import NSBarrier.NSLimitA1A2Bridge
import NSBarrier.NSInfinity
import NSBarrier.NSInfinityA1A2Bridge
import NSBarrier.NSTruncationOperator
import NSBarrier.NSSeed
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
open NSLimitA1A2Bridge
open NSInfinity
open NSInfinityA1A2Bridge
open NSTruncationOperator
open NSSeed

namespace NSCutoffA1A2Bridge

-- ============================================================
-- SECTION 1: GENERIC A1+A2 + INFINITE CUTOFF
-- ============================================================

/-- A1+A2 plus an infinite front cutoff imply eventual existence of the
    truncation-limit front for the induced finite-shell family. -/
theorem eventual_truncation_limit_exists_from_locality_A1A2_and_infinite_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold (inducedBudgetTrajectoryFamily infB) ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    EventualTruncationLimitExists (inducedBudgetTrajectoryFamily infB) := by
  exact
    eventual_truncation_limit_exists_from_locality_A1A2_with_seed
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      Gfam
      rtraj
      ν
      C_str
      C_shell
      (consistentTruncation_of_induced infB)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      hR
      hD
      (uniformSeedExtractor_of_infiniteFrontCutoff infB hcut)

/-- A1+A2 plus an infinite front cutoff imply eventual constancy
    of the limit front for the induced finite-shell family. -/
theorem limitFront_eventually_constant_from_locality_A1A2_and_infinite_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold (inducedBudgetTrajectoryFamily infB) ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    ∃ m N : ℕ, ∀ n, N ≤ n →
      limitFront (inducedBudgetTrajectoryFamily infB) n = m := by
  exact
    limitFront_eventually_constant_from_locality_A1A2_with_seed
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      Gfam
      rtraj
      ν
      C_str
      C_shell
      (consistentTruncation_of_induced infB)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      hR
      hD
      (uniformSeedExtractor_of_infiniteFrontCutoff infB hcut)

/-- A1+A2 plus an infinite front cutoff imply eventual agreement between
    sufficiently large truncations and the stabilized limit front. -/
theorem limitFront_eventually_agrees_with_truncations_from_locality_A1A2_and_infinite_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold (inducedBudgetTrajectoryFamily infB) ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    ∃ m N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront (inducedBudgetTrajectoryFamily infB) n K_max = m ∧
        limitFront (inducedBudgetTrajectoryFamily infB) n = m := by
  exact
    limitFront_eventually_agrees_with_truncations_from_locality_A1A2_with_seed
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      Gfam
      rtraj
      ν
      C_str
      C_shell
      (consistentTruncation_of_induced infB)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      hR
      hD
      (uniformSeedExtractor_of_infiniteFrontCutoff infB hcut)

#check @eventual_truncation_limit_exists_from_locality_A1A2_and_infinite_cutoff
#check @limitFront_eventually_constant_from_locality_A1A2_and_infinite_cutoff
#check @limitFront_eventually_agrees_with_truncations_from_locality_A1A2_and_infinite_cutoff

-- ============================================================
-- SECTION 2: UNIT-SHELL SPECIALIZATION
-- ============================================================

/-- Unit-shell specialization of the eventual truncation-limit existence theorem. -/
theorem eventual_truncation_limit_exists_from_locality_A1A2_unit_shell_and_infinite_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ν C_str : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      ν
      (C_str * (9 / 4 : ℝ)))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    EventualTruncationLimitExists (inducedBudgetTrajectoryFamily infB) := by
  exact
    eventual_truncation_limit_exists_from_locality_A1A2_and_infinite_cutoff
      infB
      ftraj
      Gfam
      unitShellRadiusSqTrajectory
      ν
      C_str
      (9 / 4 : ℝ)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      uniform_unitShellRadiusSq_control
      hD
      hcut

/-- Unit-shell specialization of the limit-front eventual constancy theorem. -/
theorem limitFront_eventually_constant_from_locality_A1A2_unit_shell_and_infinite_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ν C_str : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      ν
      (C_str * (9 / 4 : ℝ)))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    ∃ m N : ℕ, ∀ n, N ≤ n →
      limitFront (inducedBudgetTrajectoryFamily infB) n = m := by
  exact
    limitFront_eventually_constant_from_locality_A1A2_and_infinite_cutoff
      infB
      ftraj
      Gfam
      unitShellRadiusSqTrajectory
      ν
      C_str
      (9 / 4 : ℝ)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      uniform_unitShellRadiusSq_control
      hD
      hcut

/-- Unit-shell specialization of the eventual agreement theorem. -/
theorem limitFront_eventually_agrees_with_truncations_A1A2_unit_shell_cutoff
    (infB : InfiniteShellBudget)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ν C_str : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold
      (inducedBudgetTrajectoryFamily infB)
      ftraj
      ν
      (C_str * (9 / 4 : ℝ)))
    (hloc : UniformLocalizedProductionFromGradient (inducedBudgetTrajectoryFamily infB) ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy (inducedBudgetTrajectoryFamily infB) ftraj ν)
    (hcut : InfiniteFrontCutoff infB) :
    ∃ m N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront (inducedBudgetTrajectoryFamily infB) n K_max = m ∧
        limitFront (inducedBudgetTrajectoryFamily infB) n = m := by
  exact
    limitFront_eventually_agrees_with_truncations_from_locality_A1A2_and_infinite_cutoff
      infB
      ftraj
      Gfam
      unitShellRadiusSqTrajectory
      ν
      C_str
      (9 / 4 : ℝ)
      hCstr
      hS
      hXi
      hE
      hA
      hloc
      hgc
      h0
      hXiR
      uniform_unitShellRadiusSq_control
      hD
      hcut

#check @eventual_truncation_limit_exists_from_locality_A1A2_unit_shell_and_infinite_cutoff
#check @limitFront_eventually_constant_from_locality_A1A2_unit_shell_and_infinite_cutoff
#check @limitFront_eventually_agrees_with_truncations_A1A2_unit_shell_cutoff

end NSCutoffA1A2Bridge
