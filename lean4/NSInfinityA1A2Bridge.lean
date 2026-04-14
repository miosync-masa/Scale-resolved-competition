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

namespace NSInfinityA1A2Bridge

-- ============================================================
-- SECTION 1: GENERIC LIMIT-FRONT CONSEQUENCES
-- ============================================================

/-- If truncation-limit fronts exist eventually and the finite-shell fronts are
    uniformly eventually nonincreasing, then the limit front is eventually nonincreasing. -/
theorem limitFront_eventually_nonincreasing_of_eventual_limit_and_uniform_nonincreasing
    (btraj : BudgetTrajectoryFamily)
    (hlim : EventualTruncationLimitExists btraj)
    (hmono : UniformEventuallyNonincreasingFront btraj) :
    ∃ N : ℕ, ∀ n, N ≤ n → limitFront btraj (n + 1) ≤ limitFront btraj n := by
  rcases limitFront_spec btraj hlim with ⟨Nl, hl⟩
  rcases hmono with ⟨Nm, hm⟩
  refine ⟨max Nl Nm, ?_⟩
  intro n hn
  have hNl_n : Nl ≤ n := by
    exact le_trans (le_max_left Nl Nm) hn
  have hNl_n1 : Nl ≤ n + 1 := by
    omega
  have hNm_n : Nm ≤ n := by
    exact le_trans (le_max_right Nl Nm) hn
  rcases hl n hNl_n with ⟨K0, hK0⟩
  rcases hl (n + 1) hNl_n1 with ⟨K1, hK1⟩
  let K := max K0 K1
  have hfront0 : NSLimit.truncationFront btraj n K = limitFront btraj n := by
    exact hK0 K (le_max_left K0 K1)
  have hfront1 : NSLimit.truncationFront btraj (n + 1) K = limitFront btraj (n + 1) := by
    exact hK1 K (le_max_right K0 K1)
  calc
    limitFront btraj (n + 1)
        = NSLimit.truncationFront btraj (n + 1) K := hfront1.symm
    _ ≤ NSLimit.truncationFront btraj n K := hm K n hNm_n
    _ = limitFront btraj n := hfront0

/-- Eventual nonincrease of the limit front implies eventual constancy,
    since the limit front is nat-valued. -/
theorem limitFront_eventually_constant_of_eventual_limit_and_uniform_nonincreasing
    (btraj : BudgetTrajectoryFamily)
    (hlim : EventualTruncationLimitExists btraj)
    (hmono : UniformEventuallyNonincreasingFront btraj) :
    ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m := by
  rcases
    limitFront_eventually_nonincreasing_of_eventual_limit_and_uniform_nonincreasing
      btraj hlim hmono with
    ⟨N0, hmono0⟩
  let f : ℕ → ℕ := fun t => limitFront btraj (N0 + t)
  have hfmono : ∀ t, f (t + 1) ≤ f t := by
    intro t
    have hN0 : N0 ≤ N0 + t := by omega
    simpa [f, Nat.add_assoc] using hmono0 (N0 + t) hN0
  rcases nat_seq_eventually_constant_of_nonincreasing f hfmono with
    ⟨m, N1, hconst⟩
  refine ⟨m, N0 + N1, ?_⟩
  intro n hn
  have hN0 : N0 ≤ n := by omega
  rcases Nat.exists_eq_add_of_le hN0 with ⟨t, rfl⟩
  have ht : N1 ≤ t := by omega
  simpa [f] using hconst t ht

/-- If the limit front is eventually constant and the truncation-limit exists,
    then sufficiently large truncations agree with the stabilized limit-front value. -/
theorem limitFront_eventually_agrees_with_truncations_of_eventual_limit_and_eventual_constant
    (btraj : BudgetTrajectoryFamily)
    (hlim : EventualTruncationLimitExists btraj)
    (hconst : ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m) :
    ∃ m N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront btraj n K_max = m ∧
        limitFront btraj n = m := by
  rcases limitFront_spec btraj hlim with ⟨Nl, hl⟩
  rcases hconst with ⟨m, Nc, hc⟩
  refine ⟨m, max Nl Nc, ?_⟩
  intro n hn
  have hNl : Nl ≤ n := by
    exact le_trans (le_max_left Nl Nc) hn
  have hNc : Nc ≤ n := by
    exact le_trans (le_max_right Nl Nc) hn
  rcases hl n hNl with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K_max hK
  refine ⟨?_, hc n hNc⟩
  exact (hK0 K_max hK).trans (hc n hNc)

#check @limitFront_eventually_nonincreasing_of_eventual_limit_and_uniform_nonincreasing
#check @limitFront_eventually_constant_of_eventual_limit_and_uniform_nonincreasing
#check @limitFront_eventually_agrees_with_truncations_of_eventual_limit_and_eventual_constant

-- ============================================================
-- SECTION 2: A1+A2 -> LIMIT-FRONT CONSEQUENCES
-- ============================================================

/-- Combined A1+A2 hypotheses imply eventual nonincrease of the limit front. -/
theorem limitFront_eventually_nonincreasing_from_locality_A1A2_with_seed
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
    ∃ N : ℕ, ∀ n, N ≤ n → limitFront btraj (n + 1) ≤ limitFront btraj n := by
  have hlim : EventualTruncationLimitExists btraj :=
    eventual_truncation_limit_exists_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  have hmono : UniformEventuallyNonincreasingFront btraj :=
    uniform_eventually_nonincreasing_front_from_locality_A1A2_inst
      btraj ftraj Gfam rtraj ν C_str C_shell
      hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD
  exact
    limitFront_eventually_nonincreasing_of_eventual_limit_and_uniform_nonincreasing
      btraj hlim hmono

/-- Combined A1+A2 hypotheses imply eventual constancy of the limit front. -/
theorem limitFront_eventually_constant_from_locality_A1A2_with_seed
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
    ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m := by
  have hlim : EventualTruncationLimitExists btraj :=
    eventual_truncation_limit_exists_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  have hmono : UniformEventuallyNonincreasingFront btraj :=
    uniform_eventually_nonincreasing_front_from_locality_A1A2_inst
      btraj ftraj Gfam rtraj ν C_str C_shell
      hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD
  exact
    limitFront_eventually_constant_of_eventual_limit_and_uniform_nonincreasing
      btraj hlim hmono

/-- Combined A1+A2 hypotheses imply eventual agreement between the stabilized
    limit front and all sufficiently large truncations. -/
theorem limitFront_eventually_agrees_with_truncations_from_locality_A1A2_with_seed
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
    ∃ m N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront btraj n K_max = m ∧
        limitFront btraj n = m := by
  have hlim : EventualTruncationLimitExists btraj :=
    eventual_truncation_limit_exists_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  have hconst :
      ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m :=
    limitFront_eventually_constant_from_locality_A1A2_with_seed
      btraj ftraj Gfam rtraj ν C_str C_shell
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR hR hD hseed
  exact
    limitFront_eventually_agrees_with_truncations_of_eventual_limit_and_eventual_constant
      btraj hlim hconst

#check @limitFront_eventually_nonincreasing_from_locality_A1A2_with_seed
#check @limitFront_eventually_constant_from_locality_A1A2_with_seed
#check @limitFront_eventually_agrees_with_truncations_from_locality_A1A2_with_seed

-- ============================================================
-- SECTION 3: UNIT-SHELL SPECIALIZATION
-- ============================================================

/-- Unit-shell specialization of the limit-front eventual nonincrease theorem. -/
theorem limitFront_eventually_nonincreasing_from_locality_A1A2_unit_shell_with_seed
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
    ∃ N : ℕ, ∀ n, N ≤ n → limitFront btraj (n + 1) ≤ limitFront btraj n := by
  exact
    limitFront_eventually_nonincreasing_from_locality_A1A2_with_seed
      btraj ftraj Gfam unitShellRadiusSqTrajectory ν C_str (9 / 4 : ℝ)
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR uniform_unitShellRadiusSq_control hD hseed

/-- Unit-shell specialization of the limit-front eventual constancy theorem. -/
theorem limitFront_eventually_constant_from_locality_A1A2_unit_shell_with_seed
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
    ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m := by
  exact
    limitFront_eventually_constant_from_locality_A1A2_with_seed
      btraj ftraj Gfam unitShellRadiusSqTrajectory ν C_str (9 / 4 : ℝ)
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR uniform_unitShellRadiusSq_control hD hseed

/-- Unit-shell specialization of the eventual agreement theorem. -/
theorem limitFront_eventually_agrees_with_truncations_from_locality_A1A2_unit_shell_with_seed
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
    ∃ m N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront btraj n K_max = m ∧
        limitFront btraj n = m := by
  exact
    limitFront_eventually_agrees_with_truncations_from_locality_A1A2_with_seed
      btraj ftraj Gfam unitShellRadiusSqTrajectory ν C_str (9 / 4 : ℝ)
      hcons hCstr hS hXi hE hA hloc hgc h0 hXiR uniform_unitShellRadiusSq_control hD hseed

#check @limitFront_eventually_nonincreasing_from_locality_A1A2_unit_shell_with_seed
#check @limitFront_eventually_constant_from_locality_A1A2_unit_shell_with_seed
#check @limitFront_eventually_agrees_with_truncations_from_locality_A1A2_unit_shell_with_seed

end NSInfinityA1A2Bridge
