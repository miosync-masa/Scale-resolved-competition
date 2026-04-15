import NSBarrier.NSFiniteSourceTrajectory
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace NSFiniteSourceConditionalGronwall

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory

/-- A discrete-time enstrophy trajectory. -/
def EnstrophyTrajectory := ℕ → ℝ

#check @EnstrophyTrajectory

-- ============================================================
-- SECTION 1: DISCRETE GRONWALL
-- ============================================================

/-- Discrete Grönwall from a one-step linear inequality. -/
theorem discrete_gronwall_from_step_bound
    (E : EnstrophyTrajectory) (C : ℝ)
    (hC : 0 ≤ C)
    (hstep : ∀ n : ℕ, E (n + 1) ≤ (1 + C) * E n) :
    ∀ m : ℕ, E m ≤ (1 + C) ^ m * E 0 := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ihm =>
      have h1C : 0 ≤ 1 + C := by linarith
      have hm :
          (1 + C) * E m ≤ (1 + C) * ((1 + C) ^ m * E 0) := by
        exact mul_le_mul_of_nonneg_left ihm h1C
      calc
        E (m + 1) ≤ (1 + C) * E m := hstep m
        _ ≤ (1 + C) * ((1 + C) ^ m * E 0) := hm
        _ = (1 + C) ^ (m + 1) * E 0 := by
            simp [pow_succ, mul_left_comm, mul_comm]

/-- Eventual discrete Grönwall: once the one-step linear bound holds after time `N0`,
    the shifted trajectory is exponentially controlled. -/
theorem eventual_discrete_gronwall_from_step_bound
    (E : EnstrophyTrajectory) (C : ℝ)
    (hC : 0 ≤ C)
    (hstep :
      ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → E (n + 1) ≤ (1 + C) * E n) :
    ∃ N0 : ℕ, ∀ m : ℕ, E (N0 + m) ≤ (1 + C) ^ m * E N0 := by
  rcases hstep with ⟨N0, hN0⟩
  let F : EnstrophyTrajectory := fun m => E (N0 + m)
  have hF : ∀ m : ℕ, F (m + 1) ≤ (1 + C) * F m := by
    intro m
    have hNm : N0 ≤ N0 + m := Nat.le_add_right N0 m
    simpa [F, Nat.add_assoc] using hN0 (N0 + m) hNm
  refine ⟨N0, ?_⟩
  intro m
  simpa [F] using discrete_gronwall_from_step_bound F C hC hF m

#check @discrete_gronwall_from_step_bound
#check @eventual_discrete_gronwall_from_step_bound

-- ============================================================
-- SECTION 2: CONDITIONAL STEP BOUND FROM FINITE SOURCE CLOSURE
-- ============================================================

/-- If enstrophy increments are dominated by the total shell net source,
    and if the low-shell dissipation is controlled by `C * E(n)`,
    then the finite-source closure yields an eventual one-step linear bound. -/
theorem eventually_step_bound_of_finite_source_closure_of_cutoff
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ n : ℕ, N0 ≤ n → E (n + 1) ≤ (1 + M * C) * E n := by
  rcases eventually_finite_source_closure_of_cutoff traj M Ncut hM htail hratio with
    ⟨Nfc, hfc⟩
  rcases hDiss with ⟨Nd, hNd⟩
  refine ⟨max Nfc Nd, ?_⟩
  intro n hn
  have hNfc : Nfc ≤ n := le_trans (le_max_left Nfc Nd) hn
  have hNd' : Nd ≤ n := le_trans (le_max_right Nfc Nd) hn
  have hnet :
      shellNetSource (traj n) Finset.univ
        ≤
      M * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) :=
    hfc n hNfc
  have hdiss :
      shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n :=
    hNd n hNd'
  have hnet' :
      shellNetSource (traj n) Finset.univ ≤ (M * C) * E n := by
    have htmp :
        shellNetSource (traj n) Finset.univ ≤ M * (C * E n) := by
      exact le_trans hnet (mul_le_mul_of_nonneg_left hdiss hM)
    simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
  have hstep' : E (n + 1) ≤ E n + (M * C) * E n := by
    linarith [hinc n, hnet']
  have hEq : E n + (M * C) * E n = (1 + M * C) * E n := by ring
  rw [hEq] at hstep'
  exact hstep'

#check @eventually_step_bound_of_finite_source_closure_of_cutoff

-- ============================================================
-- SECTION 3: CONDITIONAL GRONWALL
-- ============================================================

/-- Conditional discrete Grönwall from the finite-source closure:
    if the low-shell ratio bound is eventually uniformly bounded by `M`,
    and the low-shell dissipation is eventually controlled by `C * E(n)`,
    then the enstrophy trajectory is eventually exponentially bounded. -/
theorem eventual_discrete_gronwall_of_finite_source_closure_of_cutoff
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  have hstep :
      ∃ N0 : ℕ,
        ∀ n : ℕ, N0 ≤ n → E (n + 1) ≤ (1 + M * C) * E n :=
    eventually_step_bound_of_finite_source_closure_of_cutoff
      traj E M C Ncut hM hinc htail hratio hDiss
  exact eventual_discrete_gronwall_from_step_bound E (M * C) hMC hstep

#check @eventual_discrete_gronwall_of_finite_source_closure_of_cutoff

end NSFiniteSourceConditionalGronwall
