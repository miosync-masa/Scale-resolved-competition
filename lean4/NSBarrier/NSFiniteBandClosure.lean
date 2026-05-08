import NSBarrier.NSFiniteSourceConditionalGronwall
import Mathlib.Tactic

namespace NSFiniteBandClosure

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall

/-- A time-indexed finite-band state trajectory. -/
def FiniteBandStateTrajectory (α : Type*) := ℕ → α

/-- A size functional on the finite-band state. -/
def StateSize (α : Type*) := α → ℝ

#check @FiniteBandStateTrajectory
#check @StateSize

-- ============================================================
-- SECTION 1: FINITE-BAND CLOSURE => EVENTUAL LOW-SHELL RATIO BOUND
-- ============================================================

/-- If the low-shell production is controlled by a monotone closure function of a
finite-band state, and that state is eventually bounded, then the low-shell ratio
bound `P_k ≤ M D_k` holds eventually with `M = F(B)`. -/
theorem eventually_ratio_bound_of_finite_band_state
    {K_max : ℕ} {α : Type*}
    (traj : BudgetTrajectory K_max)
    (X : FiniteBandStateTrajectory α)
    (size : StateSize α)
    (F : ℝ → ℝ)
    (Ncut : ℕ)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hsize_nonneg : ∀ n : ℕ, 0 ≤ size (X n))
    (hstate :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → size (X n) ≤ B)
    (hclosure :
      ∀ n : ℕ, ∀ k : Fin K_max, k.val < Ncut →
        (traj n).P k ≤ F (size (X n)) * (traj n).D k) :
    ∃ Nr : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (traj n).P k ≤ F B * (traj n).D k := by
  rcases hstate with ⟨Ns, B, hB⟩
  refine ⟨Ns, B, ?_, ?_⟩
  · have h0size : 0 ≤ size (X Ns) := hsize_nonneg Ns
    have hsize_le : size (X Ns) ≤ B := hB Ns (le_rfl)
    have h0B : 0 ≤ B := le_trans h0size hsize_le
    exact hFnonneg B h0B
  · intro n hn k hk
    have hsize_le : size (X n) ≤ B := hB n hn
    have hbase :
        (traj n).P k ≤ F (size (X n)) * (traj n).D k :=
      hclosure n k hk
    have hmult :
        F (size (X n)) * (traj n).D k ≤ F B * (traj n).D k := by
      exact mul_le_mul_of_nonneg_right (hFmono hsize_le) ((traj n).D_nonneg k)
    exact le_trans hbase hmult

#check @eventually_ratio_bound_of_finite_band_state

-- ============================================================
-- SECTION 2: FINITE-BAND CLOSURE => CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- Finite-band closure implies the eventual discrete Grönwall bound:
    once the tail is dissipative, the low-band state is eventually bounded by `B`,
    and low-shell dissipation is controlled by `C * E(n)`, the full enstrophy
    trajectory is eventually exponentially bounded. -/
theorem eventual_discrete_gronwall_of_finite_band_closure
    {K_max : ℕ} {α : Type*}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (X : FiniteBandStateTrajectory α)
    (size : StateSize α)
    (F : ℝ → ℝ)
    (C : ℝ) (Ncut : ℕ)
    (hC : 0 ≤ C)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hsize_nonneg : ∀ n : ℕ, 0 ≤ size (X n))
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hstate :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → size (X n) ≤ B)
    (hclosure :
      ∀ n : ℕ, ∀ k : Fin K_max, k.val < Ncut →
        (traj n).P k ≤ F (size (X n)) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ m : ℕ, E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 := by
  rcases eventually_ratio_bound_of_finite_band_state
    traj X size F Ncut hFmono hFnonneg hsize_nonneg hstate hclosure with
    ⟨Nr, B, hFB_nonneg, hratio⟩
  have hFBC_nonneg : 0 ≤ F B * C :=
    mul_nonneg hFB_nonneg hC
  have hgr :
      ∃ N0 : ℕ, ∀ m : ℕ, E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 := by
    exact
      eventual_discrete_gronwall_of_finite_source_closure_of_cutoff
        traj E (F B) C Ncut
        hFB_nonneg hFBC_nonneg
        hinc htail
        ⟨Nr, hratio⟩
        hDiss
  rcases hgr with ⟨N0, hN0⟩
  exact ⟨N0, B, hFB_nonneg, hN0⟩

#check @eventual_discrete_gronwall_of_finite_band_closure

-- ============================================================
-- SECTION 3: A SIMPLER COROLLARY FOR A CONSTANT RATIO BOUND
-- ============================================================

/-- If the finite-band closure function is already uniformly bounded by a constant `M`,
    then the previous theorem reduces to the fixed-ratio conditional Grönwall theorem. -/
theorem eventual_discrete_gronwall_of_uniform_finite_band_ratio
    {K_max : ℕ} {α : Type*}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (X : FiniteBandStateTrajectory α)
    (size : StateSize α)
    (F : ℝ → ℝ)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hC : 0 ≤ C)
    (hFM : ∀ x : ℝ, 0 ≤ x → F x ≤ M)
    (hsize_nonneg : ∀ n : ℕ, 0 ≤ size (X n))
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hclosure :
      ∀ n : ℕ, ∀ k : Fin K_max, k.val < Ncut →
        (traj n).P k ≤ F (size (X n)) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  have hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut →
            (traj n).P k ≤ M * (traj n).D k := by
    refine ⟨0, ?_⟩
    intro n _hn k hk
    have hFn : F (size (X n)) ≤ M := hFM (size (X n)) (hsize_nonneg n)
    have hbase :
        (traj n).P k ≤ F (size (X n)) * (traj n).D k :=
      hclosure n k hk
    have hmult :
        F (size (X n)) * (traj n).D k ≤ M * (traj n).D k := by
      exact mul_le_mul_of_nonneg_right hFn ((traj n).D_nonneg k)
    exact le_trans hbase hmult
  have hMC : 0 ≤ M * C := mul_nonneg hM hC
  exact
    eventual_discrete_gronwall_of_finite_source_closure_of_cutoff
      traj E M C Ncut hM hMC
      hinc htail hratio hDiss

#check @eventual_discrete_gronwall_of_uniform_finite_band_ratio

end NSFiniteBandClosure
