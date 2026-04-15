import NSBarrier.NSFiniteBandClosure
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace NSFiniteBandEnergy

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandClosure

/-- A time-indexed shell-energy trajectory. -/
def ShellEnergyTrajectory (K_max : ℕ) := ℕ → Fin K_max → ℝ

/-- Total shell energy at time `n`. -/
noncomputable def totalShellEnergy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (n : ℕ) : ℝ :=
  Finset.univ.sum (fun k : Fin K_max => Eshell n k)

/-- Low-shell energy below the cutoff `Ncut` at time `n`. -/
noncomputable def lowShellEnergy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (Ncut : ℕ) (n : ℕ) : ℝ :=
  (lowShells (K_max := K_max) Ncut).sum (fun k : Fin K_max => Eshell n k)

#check @ShellEnergyTrajectory
#check @totalShellEnergy
#check @lowShellEnergy

-- ============================================================
-- SECTION 1: BASIC LOW-SHELL ENERGY FACTS
-- ============================================================

/-- Nonnegativity of low-shell energy. -/
theorem lowShellEnergy_nonneg {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max)
    (Ncut : ℕ)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k) :
    ∀ n : ℕ, 0 ≤ lowShellEnergy Eshell Ncut n := by
  intro n
  unfold lowShellEnergy
  exact Finset.sum_nonneg (by
    intro k hk
    exact hEn n k)

/-- The low-shell energy is bounded above by the total shell energy. -/
theorem lowShellEnergy_le_totalShellEnergy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max)
    (Ncut : ℕ)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k) :
    ∀ n : ℕ, lowShellEnergy Eshell Ncut n ≤ totalShellEnergy Eshell n := by
  intro n
  unfold lowShellEnergy totalShellEnergy lowShells
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (by
      intro k hkU hknot
      exact hEn n k)

#check @lowShellEnergy_nonneg
#check @lowShellEnergy_le_totalShellEnergy

/-- If the total shell energy is eventually bounded, then the low-shell energy
    is eventually bounded by the same constant. -/
theorem eventually_bounded_lowShellEnergy_of_totalShellEnergy_bound {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max)
    (Ncut : ℕ)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ Ns : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, Ns ≤ n → lowShellEnergy Eshell Ncut n ≤ B := by
  rcases hEtot with ⟨Ns, B, hB⟩
  refine ⟨Ns, B, ?_⟩
  intro n hn
  exact le_trans
    (lowShellEnergy_le_totalShellEnergy Eshell Ncut hEn n)
    (hB n hn)

#check @eventually_bounded_lowShellEnergy_of_totalShellEnergy_bound

-- ============================================================
-- SECTION 2: FINITE-BAND CLOSURE WITH LOW-SHELL ENERGY AS STATE
-- ============================================================

/-- If the low-shell production is controlled by a monotone closure function
    of the low-shell energy, and the total shell energy is eventually bounded,
    then the enstrophy trajectory is eventually exponentially bounded. -/
theorem eventual_discrete_gronwall_of_lowShellEnergy_closure
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (F : ℝ → ℝ)
    (C : ℝ) (Ncut : ℕ)
    (hC : 0 ≤ C)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hclosure :
      ∀ n : ℕ, ∀ k : Fin K_max, k.val < Ncut →
        (traj n).P k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ m : ℕ, E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 := by
  let X : FiniteBandStateTrajectory ℝ := fun n => lowShellEnergy Eshell Ncut n
  let size : StateSize ℝ := fun x => x
  have hsize_nonneg : ∀ n : ℕ, 0 ≤ size (X n) := by
    intro n
    exact lowShellEnergy_nonneg Eshell Ncut hEn n
  have hstate :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → size (X n) ≤ B := by
    simpa [X, size] using
      eventually_bounded_lowShellEnergy_of_totalShellEnergy_bound Eshell Ncut hEn hEtot
  exact
    eventual_discrete_gronwall_of_finite_band_closure
      traj E X size F C Ncut
      hC hFmono hFnonneg hsize_nonneg
      hinc htail hstate hclosure hDiss

#check @eventual_discrete_gronwall_of_lowShellEnergy_closure

-- ============================================================
-- SECTION 3: A SIMPLE COROLLARY WITH A UNIFORM ENERGY-BASED RATIO BOUND
-- ============================================================

/-- If the closure function is uniformly bounded by a constant `M`
    on the relevant low-shell energy range, then one gets the fixed-ratio
    conditional discrete Grönwall theorem as a corollary. -/
theorem eventual_discrete_gronwall_of_uniform_lowShellEnergy_ratio
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (F : ℝ → ℝ)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hC : 0 ≤ C)
    (hFM : ∀ x : ℝ, 0 ≤ x → F x ≤ M)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hclosure :
      ∀ n : ℕ, ∀ k : Fin K_max, k.val < Ncut →
        (traj n).P k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n)
    (_hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_finite_band_ratio
      traj E (fun n => lowShellEnergy Eshell Ncut n) (fun x => x) F M C Ncut
      hM hC hFM
      (by
        intro n
        exact lowShellEnergy_nonneg Eshell Ncut hEn n)
      hinc htail hclosure hDiss

#check @eventual_discrete_gronwall_of_uniform_lowShellEnergy_ratio

end NSFiniteBandEnergy
