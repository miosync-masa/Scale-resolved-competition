import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import NSBarrier.NSLimit
import NSBarrier.NSAnalyticA2
import NSBarrier.NSAnalyticA2Bridge
import NSBarrier.NSUniformA2Bridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSUniformBridge
open NSAnalyticA2
open NSAnalyticA2Bridge
open NSUniformA2Bridge
open NSLimit

namespace NSLimitA2Bridge

-- ============================================================
-- SECTION 1: UNIFORM SEED BOUNDS
-- ============================================================

/-- A uniform front bound at a specific threshold time `N`. -/
def UniformFrontSeedAt
    (btraj : BudgetTrajectoryFamily)
    (N M : ℕ) : Prop :=
  ∀ K_max, jumpFront ((btraj K_max) N) ≤ M

/-- A seed extractor:
    whenever a common threshold `N` supports eventual nonincrease,
    one can produce a uniform bound at time `N`. -/
def UniformSeedExtractor
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∀ N,
    (∀ K_max n, N ≤ n → jumpFront ((btraj K_max) (n + 1)) ≤ jumpFront ((btraj K_max) n)) →
    ∃ M, UniformFrontSeedAt btraj N M

#check @UniformFrontSeedAt
#check @UniformSeedExtractor

-- ============================================================
-- SECTION 2: FROM NONINCREASING + SEED TO UNIFORM BOUND
-- ============================================================

/-- A common threshold-time seed bound plus eventual nonincrease yields
    a uniform eventual bound on the front. -/
theorem uniform_eventually_bounded_of_threshold_seed
    (btraj : BudgetTrajectoryFamily)
    (N M : ℕ)
    (hmono :
      ∀ K_max n, N ≤ n → jumpFront ((btraj K_max) (n + 1)) ≤ jumpFront ((btraj K_max) n))
    (hseed : UniformFrontSeedAt btraj N M) :
    UniformEventuallyBoundedFront btraj := by
  refine ⟨M, N, ?_⟩
  intro K_max n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨t, rfl⟩
  let f : ℕ → ℕ := fun s => jumpFront ((btraj K_max) (N + s))
  have hfmono : ∀ s, f (s + 1) ≤ f s := by
    intro s
    have hNs : N ≤ N + s := by omega
    simpa [f, Nat.add_assoc] using hmono K_max (N + s) hNs
  have htail : f t ≤ f 0 := by
    exact nonincreasing_tail_le f hfmono (show 0 ≤ t by omega)
  have hbase : f 0 ≤ M := by
    simpa [f] using hseed K_max
  have hfinal : f t ≤ M := le_trans htail hbase
  simpa [f]

#check @uniform_eventually_bounded_of_threshold_seed

-- ============================================================
-- SECTION 3: A2 -> UNIFORM EVENTUAL BOUND
-- ============================================================

/-- Uniform A2 radius/profile hypotheses imply a uniform eventual front bound,
    provided one can extract a uniform seed bound at the common nonincrease threshold. -/
theorem uniform_eventually_bounded_from_uniform_A2_radius_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    UniformEventuallyBoundedFront btraj := by
  rcases
    uniform_eventually_nonincreasing_front_from_fourier_inst_of_radius
      btraj ftraj rtraj ν C_shell hS hE hA hP h0 hXiR hR hD with
    ⟨N, hN⟩
  rcases hseed N hN with ⟨M, hM⟩
  exact uniform_eventually_bounded_of_threshold_seed btraj N M hN hM

/-- Unit-shell specialization of the previous theorem, with explicit shell constant 9/4. -/
theorem uniform_eventually_bounded_from_uniform_A2_unit_shell_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    UniformEventuallyBoundedFront btraj := by
  exact
    uniform_eventually_bounded_from_uniform_A2_radius_with_seed
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD hseed

#check @uniform_eventually_bounded_from_uniform_A2_radius_with_seed
#check @uniform_eventually_bounded_from_uniform_A2_unit_shell_with_seed

-- ============================================================
-- SECTION 4: A2 -> TRUNCATION LIMIT EXISTENCE
-- ============================================================

/-- Uniform A2 hypotheses plus truncation consistency imply eventual existence
    of the truncation-limit front, once a uniform seed extractor is available. -/
theorem eventual_truncation_limit_exists_from_uniform_A2_radius_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hcons : ConsistentTruncation btraj)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    EventualTruncationLimitExists btraj := by
  have hbound : UniformEventuallyBoundedFront btraj :=
    uniform_eventually_bounded_from_uniform_A2_radius_with_seed
      btraj ftraj rtraj ν C_shell
      hS hE hA hP h0 hXiR hR hD hseed
  exact
    NSLimit.eventual_truncation_limit_exists_of_uniform_bound
      btraj hcons hbound

/-- Unit-shell specialization of the previous theorem. -/
theorem eventual_truncation_limit_exists_from_uniform_A2_unit_shell_with_seed
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hcons : ConsistentTruncation btraj)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hseed : UniformSeedExtractor btraj) :
    EventualTruncationLimitExists btraj := by
  exact
    eventual_truncation_limit_exists_from_uniform_A2_radius_with_seed
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hcons hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD hseed

#check @eventual_truncation_limit_exists_from_uniform_A2_radius_with_seed
#check @eventual_truncation_limit_exists_from_uniform_A2_unit_shell_with_seed

end NSLimitA2Bridge
