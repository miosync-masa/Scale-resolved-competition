import NSBarrier.NSFiniteSourceClosure
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace NSFiniteSourceTrajectory

open NSFiniteSource
open NSFiniteSourceClosure

/-- The fixed low-shell set below the cutoff `Ncut`. -/
noncomputable def lowShells {K_max : ℕ} (Ncut : ℕ) : Finset (Fin K_max) :=
  Finset.univ.filter (fun k : Fin K_max => k.val < Ncut)

#check @BudgetTrajectory
#check @lowShells

/-- Eventual finite-source reduction with a fixed cutoff:
    once all shells above `Ncut` are eventually dissipative,
    the total net source is eventually controlled by the low-shell net source. -/
theorem eventually_finite_source_reduction_of_cutoff {K_max : ℕ}
    (traj : BudgetTrajectory K_max) (Ncut : ℕ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k) :
    ∃ N0 : ℕ,
      ∀ n : ℕ, N0 ≤ n →
        shellNetSource (traj n) Finset.univ
          ≤
        shellNetSource (traj n) (lowShells (K_max := K_max) Ncut) := by
  rcases htail with ⟨Nt, hNt⟩
  refine ⟨Nt, ?_⟩
  intro n hn
  exact
    finite_source_reduction_of_cutoff
      (traj n) Ncut
      (hNt n hn)

#check @eventually_finite_source_reduction_of_cutoff

/-- Eventual finite-source closure with a fixed cutoff:
    if high shells are eventually dissipative and low shells satisfy an eventual
    bounded ratio `P_k ≤ M D_k`, then the total net shell source is eventually
    controlled by `M` times the low-shell dissipation. -/
theorem eventually_finite_source_closure_of_cutoff {K_max : ℕ}
    (traj : BudgetTrajectory K_max) (M : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k) :
    ∃ N0 : ℕ,
      ∀ n : ℕ, N0 ≤ n →
        shellNetSource (traj n) Finset.univ
          ≤
        M * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) := by
  rcases htail with ⟨Nt, hNt⟩
  rcases hratio with ⟨Nr, hNr⟩
  refine ⟨max Nt Nr, ?_⟩
  intro n hn
  have hNt' : Nt ≤ n := le_trans (le_max_left Nt Nr) hn
  have hNr' : Nr ≤ n := le_trans (le_max_right Nt Nr) hn
  exact
    finite_source_closure_of_cutoff
      (traj n) M Ncut hM
      (hNt n hNt')
      (hNr n hNr')

#check @eventually_finite_source_closure_of_cutoff

/-- Barrier-specialized eventual closure with a fixed cutoff:
    if the barrier eventually enforces tail dissipation above `Ncut`,
    and the low-shell ratio bound eventually holds below `Ncut`,
    then the total net source is eventually controlled by low-shell dissipation. -/
theorem eventually_finite_source_closure_of_barrier_fixed_cutoff {K_max : ℕ}
    (traj : BudgetTrajectory K_max) (Φ ν M : ℝ) (Ncut : ℕ)
    (_hν : 0 < ν)
    (hM : 0 ≤ M)
    (_hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max, (traj n).D k < (traj n).P k → Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k) :
    ∃ N0 : ℕ,
      ∀ n : ℕ, N0 ≤ n →
        shellNetSource (traj n) Finset.univ
          ≤
        M * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) := by
  exact
    eventually_finite_source_closure_of_cutoff
      traj M Ncut hM htail hratio

#check @eventually_finite_source_closure_of_barrier_fixed_cutoff

end NSFiniteSourceTrajectory
