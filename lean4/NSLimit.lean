import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSUniformBridge

namespace NSLimit

-- ============================================================
-- SECTION 1: TRUNCATION-SIDE FRONT SEQUENCES
-- ============================================================

/-- The front at time `n` for truncation level `K_max`. -/
noncomputable def truncationFront
    (btraj : BudgetTrajectoryFamily) (n K_max : ℕ) : ℕ :=
  jumpFront ((btraj K_max) n)

/-- Eventual constancy of the truncation-front sequence in `K_max`
    at a fixed time `n`. -/
def TruncationLimitExistsAt
    (btraj : BudgetTrajectoryFamily) (n : ℕ) : Prop :=
  ∃ m K0 : ℕ, ∀ K_max, K0 ≤ K_max → truncationFront btraj n K_max = m

/-- A global eventual version: after time `N`, each fixed time-slice has
    a well-defined truncation-limit front. -/
def EventualTruncationLimitExists
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → TruncationLimitExistsAt btraj n

-- ============================================================
-- SECTION 2: MONOTONE + BOUNDED NAT SEQUENCES
-- ============================================================

/-- A monotone nondecreasing nat-valued sequence bounded above by `M`
    is eventually constant. -/
theorem nat_seq_eventually_constant_of_monotone_bounded
    (f : ℕ → ℕ) (M : ℕ)
    (hmono : ∀ n, f n ≤ f (n + 1))
    (hbound : ∀ n, f n ≤ M) :
    ∃ m K0 : ℕ, ∀ n, K0 ≤ n → f n = m := by
  let g : ℕ → ℕ := fun n => M - f n
  have hgmono : ∀ n, g (n + 1) ≤ g n := by
    intro n
    unfold g
    have hn : f n ≤ f (n + 1) := hmono n
    omega
  rcases nat_seq_eventually_constant_of_nonincreasing g hgmono with
    ⟨m, K0, hconst⟩
  have hK0 : g K0 = m := hconst K0 le_rfl
  refine ⟨f K0, K0, ?_⟩
  intro n hn
  have hg : g n = m := hconst n hn
  unfold g at hg hK0
  have hbn : f n ≤ M := hbound n
  have hbK : f K0 ≤ M := hbound K0
  omega

#check @nat_seq_eventually_constant_of_monotone_bounded

-- ============================================================
-- SECTION 3: LIMIT EXISTENCE FROM CONSISTENCY + UNIFORM BOUND
-- ============================================================

/-- If the truncation family is monotone in `K_max` and uniformly bounded
    at a fixed time `n`, then the truncation-front sequence stabilizes
    for large enough `K_max`. -/
theorem truncation_limit_exists_of_consistent_bounded
    (btraj : BudgetTrajectoryFamily)
    (hcons : ConsistentTruncation btraj)
    (n M : ℕ)
    (hbound : ∀ K_max, truncationFront btraj n K_max ≤ M) :
    TruncationLimitExistsAt btraj n := by
  let f : ℕ → ℕ := fun K_max => truncationFront btraj n K_max
  have hmono : ∀ K_max, f K_max ≤ f (K_max + 1) := by
    intro K_max
    exact hcons K_max n
  have hbd : ∀ K_max, f K_max ≤ M := by
    intro K_max
    exact hbound K_max
  rcases nat_seq_eventually_constant_of_monotone_bounded f M hmono hbd with
    ⟨m, K0, hK0⟩
  refine ⟨m, K0, ?_⟩
  intro K_max hK
  exact hK0 K_max hK

/-- Uniform eventual boundedness plus truncation consistency imply
    eventual existence of the truncation-limit front. -/
theorem eventual_truncation_limit_exists_of_uniform_bound
    (btraj : BudgetTrajectoryFamily)
    (hcons : ConsistentTruncation btraj)
    (hbound : UniformEventuallyBoundedFront btraj) :
    EventualTruncationLimitExists btraj := by
  rcases hbound with ⟨M, N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  apply truncation_limit_exists_of_consistent_bounded btraj hcons n M
  intro K_max
  exact hN K_max n hn

#check @truncation_limit_exists_of_consistent_bounded
#check @eventual_truncation_limit_exists_of_uniform_bound

-- ============================================================
-- SECTION 4: CONSEQUENCES OF UNIFORM EVENTUAL CONSTANCY
-- ============================================================

/-- If the front is uniformly eventually constant across all truncations,
    then the truncation-limit front exists trivially. -/
theorem eventual_truncation_limit_exists_of_uniform_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    EventualTruncationLimitExists btraj := by
  rcases hconst with ⟨m, N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  refine ⟨m, 0, ?_⟩
  intro K_max _hK
  exact hN K_max n hn

/-- Uniform eventual constancy implies a truncation-independent front value
    after the common threshold time. -/
theorem truncation_independent_limit_of_uniform_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    ∃ m N, ∀ K_max n, N ≤ n → truncationFront btraj n K_max = m := by
  rcases hconst with ⟨m, N, hN⟩
  exact ⟨m, N, hN⟩

#check @eventual_truncation_limit_exists_of_uniform_constant
#check @truncation_independent_limit_of_uniform_constant

-- ============================================================
-- SECTION 5: LIMIT-SIDE CONSEQUENCES FROM UNIFORM FOURIER INPUT
-- ============================================================

/-- If the uniform Fourier-side hypotheses give a uniform eventual front bound,
    then truncation consistency upgrades this to eventual existence of a
    truncation-limit front. -/
theorem eventual_truncation_limit_exists_from_uniform_fourier_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hcons : ConsistentTruncation btraj)
    (_hS : UniformStrainSupNonneg ftraj)
    (_hE : UniformShellEnergyNonneg ftraj)
    (_hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (_hP : UniformProductionFromStrainSup btraj ftraj)
    (_hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (_hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hbound : UniformEventuallyBoundedFront btraj) :
    EventualTruncationLimitExists btraj := by
  exact eventual_truncation_limit_exists_of_uniform_bound btraj hcons hbound

/-- A stronger but simpler route: if one has already proved uniform eventual constancy,
    then the truncation-limit front exists with a common value across all truncations. -/
theorem truncation_independent_limit_from_uniform_fourier_constant
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (_hS : UniformStrainSupNonneg ftraj)
    (_hE : UniformShellEnergyNonneg ftraj)
    (_hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (_hP : UniformProductionFromStrainSup btraj ftraj)
    (_hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (_hD : UniformDissipationFromEnergy btraj ftraj ν)
    (hconst : UniformEventuallyConstantFront btraj) :
    ∃ m N, ∀ K_max n, N ≤ n → truncationFront btraj n K_max = m := by
  exact truncation_independent_limit_of_uniform_constant btraj hconst

#check @truncationFront
#check @TruncationLimitExistsAt
#check @EventualTruncationLimitExists
#check @nat_seq_eventually_constant_of_monotone_bounded
#check @truncation_limit_exists_of_consistent_bounded
#check @eventual_truncation_limit_exists_of_uniform_bound
#check @eventual_truncation_limit_exists_of_uniform_constant
#check @truncation_independent_limit_of_uniform_constant
#check @eventual_truncation_limit_exists_from_uniform_fourier_inst
#check @truncation_independent_limit_from_uniform_fourier_constant

end NSLimit
