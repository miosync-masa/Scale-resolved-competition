import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import NSBarrier.NSLimit
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSUniformBridge
open NSLimit
namespace NSInfinity

-- ============================================================
-- SECTION 1: LIMIT FRONT
-- ============================================================

open Classical in
/-- A limit-front selector extracted from truncation-limit existence at each time.
    It is defined as the least stabilized truncation value whenever such a value exists,
    and `0` otherwise. -/
noncomputable def limitFront
    (btraj : BudgetTrajectoryFamily) : ℕ → ℕ :=
  fun n =>
    if h : NSLimit.TruncationLimitExistsAt btraj n then
      Nat.find h
    else
      0

/-- Uniqueness of the stabilized truncation value at a fixed time. -/
theorem truncation_limit_value_unique
    (btraj : BudgetTrajectoryFamily) (n : ℕ)
    {m1 K1 m2 K2 : ℕ}
    (h1 : ∀ K_max, K1 ≤ K_max → NSLimit.truncationFront btraj n K_max = m1)
    (h2 : ∀ K_max, K2 ≤ K_max → NSLimit.truncationFront btraj n K_max = m2) :
    m1 = m2 := by
  have h1' : NSLimit.truncationFront btraj n (max K1 K2) = m1 :=
    h1 (max K1 K2) (le_max_left K1 K2)
  have h2' : NSLimit.truncationFront btraj n (max K1 K2) = m2 :=
    h2 (max K1 K2) (le_max_right K1 K2)
  exact h1'.symm.trans h2'

/-- If a truncation-limit exists at time `n`, then `limitFront` agrees with it. -/
theorem limitFront_eq_of_exists
    (btraj : BudgetTrajectoryFamily) {n : ℕ}
    (hex : NSLimit.TruncationLimitExistsAt btraj n) :
    ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
      NSLimit.truncationFront btraj n K_max = limitFront btraj n := by
  classical
  rcases hex with ⟨m, K0, hK0⟩
  unfold limitFront
  split_ifs with h
  · exact Nat.find_spec h
  · exact absurd ⟨m, K0, hK0⟩ h

/-- Beyond the threshold supplied by `EventualTruncationLimitExists`,
    the truncation-limit front exists and agrees with `limitFront`. -/
theorem limitFront_spec
    (btraj : BudgetTrajectoryFamily)
    (hlim : NSLimit.EventualTruncationLimitExists btraj) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ K0 : ℕ, ∀ K_max, K0 ≤ K_max →
        NSLimit.truncationFront btraj n K_max = limitFront btraj n := by
  rcases hlim with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact limitFront_eq_of_exists btraj (hN n hn)

-- ============================================================
-- SECTION 2: EVENTUAL CONSTANCY OF THE LIMIT FRONT
-- ============================================================

/-- If the truncation family is uniformly eventually constant with common value `m`,
    then the limit front is eventually equal to the same `m`. -/
theorem limitFront_eventually_constant_of_uniform_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    ∃ m N : ℕ, ∀ n, N ≤ n → limitFront btraj n = m := by
  rcases hconst with ⟨m, N, hN⟩
  refine ⟨m, N, ?_⟩
  intro n hn
  have hex : NSLimit.TruncationLimitExistsAt btraj n := by
    refine ⟨m, 0, ?_⟩
    intro K_max _
    exact hN K_max n hn
  rcases limitFront_eq_of_exists btraj hex with ⟨K0, hK0⟩
  have h1 : NSLimit.truncationFront btraj n K0 = limitFront btraj n :=
    hK0 K0 le_rfl
  have h2 : NSLimit.truncationFront btraj n K0 = m :=
    hN K0 n hn
  exact h1.symm.trans h2

/-- If the truncation family is uniformly eventually constant,
    then the limit front agrees with the same common value. -/
theorem limitFront_agrees_with_uniform_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    ∃ m N : ℕ, ∀ K_max n, N ≤ n →
      NSLimit.truncationFront btraj n K_max = m ∧
      limitFront btraj n = m := by
  rcases hconst with ⟨m, N, hN⟩
  rcases limitFront_eventually_constant_of_uniform_constant btraj ⟨m, N, hN⟩ with
    ⟨m', N', hN'⟩
  have hm : m' = m := by
    let n0 := max N N'
    have h1 : limitFront btraj n0 = m' := hN' n0 (le_max_right N N')
    have h2 : limitFront btraj n0 = m := by
      have hex : NSLimit.TruncationLimitExistsAt btraj n0 := by
        refine ⟨m, 0, ?_⟩
        intro K_max _
        exact hN K_max n0 (le_max_left N N')
      rcases limitFront_eq_of_exists btraj hex with ⟨K0, hK0⟩
      have htr : NSLimit.truncationFront btraj n0 K0 = limitFront btraj n0 :=
        hK0 K0 le_rfl
      have hconstK : NSLimit.truncationFront btraj n0 K0 = m :=
        hN K0 n0 (le_max_left N N')
      exact htr.symm.trans hconstK
    exact h1.symm.trans h2
  refine ⟨m, max N N', ?_⟩
  intro K_max n hn
  have hNle : N ≤ n := le_trans (le_max_left N N') hn
  have hN'le : N' ≤ n := le_trans (le_max_right N N') hn
  refine ⟨hN K_max n hNle, ?_⟩
  simpa [hm] using hN' n hN'le

end NSInfinity
