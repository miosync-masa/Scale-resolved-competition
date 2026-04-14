import NSBarrier.Basic
import NSBarrier.NSUniform
import NSBarrier.NSLimit
import NSBarrier.NSLimitA2Bridge
import NSBarrier.NSTruncationOperator
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open NSUniform
open NSLimit
open NSLimitA2Bridge
open NSTruncationOperator

namespace NSSeed

-- ============================================================
-- SECTION 1: INFINITE-SIDE SEED HYPOTHESES
-- ============================================================

/-- At time `n`, all shells strictly above `M` are already inactive
    in the infinite shell budget, in the sense `P_inf ≤ D_inf`. -/
def InfiniteFrontCutoffAt
    (infB : InfiniteShellBudget) (n M : ℕ) : Prop :=
  ∀ k : ℕ, M < k → infB.P_inf n k ≤ infB.D_inf n k

/-- Every time-slice admits some finite front cutoff. -/
def InfiniteFrontCutoff
    (infB : InfiniteShellBudget) : Prop :=
  ∀ n : ℕ, ∃ M : ℕ, InfiniteFrontCutoffAt infB n M

#check @InfiniteFrontCutoffAt
#check @InfiniteFrontCutoff

-- ============================================================
-- SECTION 2: INFINITE CUTOFF -> UNIFORM SEED AT A FIXED TIME
-- ============================================================

/-- A tail-inactivity bound at time `n` gives a uniform seed bound
    for all finite truncations at the same time. -/
theorem uniformFrontSeedAt_of_infiniteFrontCutoffAt
    (infB : InfiniteShellBudget) (n M : ℕ)
    (hcut : InfiniteFrontCutoffAt infB n M) :
    UniformFrontSeedAt (inducedBudgetTrajectoryFamily infB) n M := by
  intro K_max
  classical
  let sb : ShellBudget K_max := (inducedBudgetTrajectoryFamily infB K_max) n
  by_cases hne : (activeShells sb).Nonempty
  · let k : Fin K_max := (activeShells sb).max' hne
    have hk_act : isSD sb k := by
      exact (Finset.mem_filter.mp (Finset.max'_mem (activeShells sb) hne)).2
    have hk_le : k.val ≤ M := by
      by_contra hk_gt
      have hk_gt' : M < k.val := Nat.lt_of_not_ge hk_gt
      have hcutk : infB.P_inf n k.val ≤ infB.D_inf n k.val := hcut k.val hk_gt'
      dsimp [sb, inducedBudgetTrajectoryFamily, inducedShellBudget, isSD, restrictShell] at hk_act
      linarith
    have hfront : jumpFront sb = k.val := by
      simp [sb, jumpFront, hne, k]
    calc
      jumpFront sb = k.val := hfront
      _ ≤ M := hk_le
  · have hfront0 : jumpFront sb = 0 := by
      simp [sb, jumpFront, hne]
    rw [hfront0]
    exact Nat.zero_le M

#check @uniformFrontSeedAt_of_infiniteFrontCutoffAt

-- ============================================================
-- SECTION 3: INFINITE CUTOFF -> UNIFORM SEED EXTRACTOR
-- ============================================================

/-- If every time-slice admits some infinite-shell front cutoff,
    then the induced finite-truncation family has a uniform seed extractor. -/
theorem uniformSeedExtractor_of_infiniteFrontCutoff
    (infB : InfiniteShellBudget)
    (hcut : InfiniteFrontCutoff infB) :
    UniformSeedExtractor (inducedBudgetTrajectoryFamily infB) := by
  intro N _hmono
  rcases hcut N with ⟨M, hM⟩
  exact ⟨M, uniformFrontSeedAt_of_infiniteFrontCutoffAt infB N M hM⟩

#check @uniformSeedExtractor_of_infiniteFrontCutoff

-- ============================================================
-- SECTION 4: CONSEQUENCES FOR BOUNDS AND LIMITS
-- ============================================================

/-- If the induced truncation family is eventually nonincreasing and the infinite
    shell budget has a front cutoff at every time, then the induced family is
    uniformly eventually bounded. -/
theorem uniform_eventually_bounded_of_infiniteFrontCutoff
    (infB : InfiniteShellBudget)
    (hcut : InfiniteFrontCutoff infB)
    (hmono : UniformEventuallyNonincreasingFront (inducedBudgetTrajectoryFamily infB)) :
    UniformEventuallyBoundedFront (inducedBudgetTrajectoryFamily infB) := by
  have hseed : UniformSeedExtractor (inducedBudgetTrajectoryFamily infB) :=
    uniformSeedExtractor_of_infiniteFrontCutoff infB hcut
  rcases hmono with ⟨N, hN⟩
  rcases hseed N hN with ⟨M, hM⟩
  exact
    uniform_eventually_bounded_of_threshold_seed
      (inducedBudgetTrajectoryFamily infB)
      N M hN hM

/-- If the induced truncation family is eventually nonincreasing and the infinite
    shell budget has a front cutoff at every time, then the truncation-limit front
    exists eventually. -/
theorem eventual_truncation_limit_exists_of_infiniteFrontCutoff
    (infB : InfiniteShellBudget)
    (hcut : InfiniteFrontCutoff infB)
    (hmono : UniformEventuallyNonincreasingFront (inducedBudgetTrajectoryFamily infB)) :
    EventualTruncationLimitExists (inducedBudgetTrajectoryFamily infB) := by
  have hbound : UniformEventuallyBoundedFront (inducedBudgetTrajectoryFamily infB) :=
    uniform_eventually_bounded_of_infiniteFrontCutoff infB hcut hmono
  exact
    eventual_truncation_limit_exists_of_uniform_bound
      (inducedBudgetTrajectoryFamily infB)
      (consistentTruncation_of_induced infB)
      hbound

#check @uniform_eventually_bounded_of_infiniteFrontCutoff
#check @eventual_truncation_limit_exists_of_infiniteFrontCutoff

end NSSeed
