import NSBarrier.NSFiniteSourceConditionalGronwall
import Mathlib.Tactic

namespace NSIntegratedHinc

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall

-- ============================================================
-- SECTION 1: SCALING A SHELL BUDGET BY A TIME STEP
-- ============================================================

/-- Scale a shell budget by a nonnegative factor `α`.  This is the natural way
to pass from an instantaneous shell budget to an integrated shell budget
over a time interval of length `α = Δt`. -/
noncomputable def scaleShellBudget {K_max : ℕ}
    (α : ℝ) (hα : 0 ≤ α)
    (sb : ShellBudget K_max) : ShellBudget K_max where
  P := fun k => α * sb.P k
  D := fun k => α * sb.D k
  D_nonneg := by
    intro k
    exact mul_nonneg hα (sb.D_nonneg k)

#check @scaleShellBudget

/-- Scale an entire budget trajectory by a nonnegative factor `α`. -/
noncomputable def scaleBudgetTrajectory {K_max : ℕ}
    (α : ℝ) (hα : 0 ≤ α)
    (traj : BudgetTrajectory K_max) : BudgetTrajectory K_max :=
  fun n => scaleShellBudget α hα (traj n)

#check @scaleBudgetTrajectory

theorem shellNetSource_scale {K_max : ℕ}
    (α : ℝ) (hα : 0 ≤ α)
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) :
    shellNetSource (scaleShellBudget α hα sb) S
      =
    α * shellNetSource sb S := by
  unfold shellNetSource scaleShellBudget
  simp [mul_sub, Finset.mul_sum]

theorem shellProductionSource_scale {K_max : ℕ}
    (α : ℝ) (hα : 0 ≤ α)
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) :
    shellProductionSource (scaleShellBudget α hα sb) S
      =
    α * shellProductionSource sb S := by
  unfold shellProductionSource scaleShellBudget
  simp [Finset.mul_sum]

theorem shellDissipationSource_scale {K_max : ℕ}
    (α : ℝ) (hα : 0 ≤ α)
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) :
    shellDissipationSource (scaleShellBudget α hα sb) S
      =
    α * shellDissipationSource sb S := by
  unfold shellDissipationSource scaleShellBudget
  simp [Finset.mul_sum]

#check @shellNetSource_scale
#check @shellProductionSource_scale
#check @shellDissipationSource_scale

-- ============================================================
-- SECTION 2: INTEGRATED hinc -> DISCRETE hinc FOR THE SCALED TRAJECTORY
-- ============================================================

/-- An integrated one-step inequality yields the discrete `hinc` inequality
for the scaled shell-budget trajectory. -/
theorem hinc_of_integrated_shellNetSource {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Δt : ℝ) (hΔt : 0 ≤ Δt)
    (hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n ≤ Δt * shellNetSource (traj n) Finset.univ) :
    ∀ n : ℕ,
      E (n + 1) - E n
        ≤ shellNetSource (scaleBudgetTrajectory Δt hΔt traj n) Finset.univ := by
  intro n
  simpa [scaleBudgetTrajectory, shellNetSource_scale] using hinc_int n

#check @hinc_of_integrated_shellNetSource

-- ============================================================
-- SECTION 3: EVENTUAL STRUCTURAL HYPOTHESES SURVIVE SCALING
-- ============================================================

theorem eventually_tail_dissipative_of_scaled {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Δt : ℝ) (hΔt : 0 ≤ Δt)
    (Ncut : ℕ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k) :
    ∃ Nt : ℕ,
      ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, Ncut ≤ k.val →
          (scaleBudgetTrajectory Δt hΔt traj n).P k
            ≤
          (scaleBudgetTrajectory Δt hΔt traj n).D k := by
  rcases htail with ⟨Nt, hNt⟩
  refine ⟨Nt, ?_⟩
  intro n hn k hk
  have hbase : (traj n).P k ≤ (traj n).D k := hNt n hn k hk
  simpa [scaleBudgetTrajectory, scaleShellBudget]
    using mul_le_mul_of_nonneg_left hbase hΔt

theorem eventually_ratio_bound_of_scaled {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Δt : ℝ) (hΔt : 0 ≤ Δt)
    (M : ℝ) (Ncut : ℕ)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k) :
    ∃ Nr : ℕ,
      ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (scaleBudgetTrajectory Δt hΔt traj n).P k
            ≤
          M * (scaleBudgetTrajectory Δt hΔt traj n).D k := by
  rcases hratio with ⟨Nr, hNr⟩
  refine ⟨Nr, ?_⟩
  intro n hn k hk
  have hbase : (traj n).P k ≤ M * (traj n).D k := hNr n hn k hk
  simpa [scaleBudgetTrajectory, scaleShellBudget, mul_assoc, mul_left_comm, mul_comm]
    using mul_le_mul_of_nonneg_left hbase hΔt

theorem eventually_scaled_lowShell_dissipation_bound {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Δt : ℝ) (hΔt : 0 ≤ Δt)
    (C : ℝ) (Ncut : ℕ)
    (hDiss_int :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          Δt * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (scaleBudgetTrajectory Δt hΔt traj n)
          (lowShells (K_max := K_max) Ncut)
            ≤ C * E n := by
  rcases hDiss_int with ⟨Nd, hNd⟩
  refine ⟨Nd, ?_⟩
  intro n hn
  simpa [scaleBudgetTrajectory, shellDissipationSource_scale]
    using hNd n hn

#check @eventually_tail_dissipative_of_scaled
#check @eventually_ratio_bound_of_scaled
#check @eventually_scaled_lowShell_dissipation_bound

-- ============================================================
-- SECTION 4: INTEGRATED hinc -> CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- Integrated shell-budget control yields the same conditional discrete Grönwall
bound after passing to the scaled budget trajectory. -/
theorem eventual_discrete_gronwall_of_integrated_cutoff {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Δt M C : ℝ) (Ncut : ℕ)
    (hΔt : 0 ≤ Δt)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n ≤ Δt * shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k)
    (hDiss_int :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          Δt * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  let trajΔ : BudgetTrajectory K_max := scaleBudgetTrajectory Δt hΔt traj
  have hincΔ :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (trajΔ n) Finset.univ := by
    intro n
    simpa [trajΔ] using hinc_of_integrated_shellNetSource traj E Δt hΔt hinc_int n
  have htailΔ :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (trajΔ n).P k ≤ (trajΔ n).D k := by
    simpa [trajΔ] using eventually_tail_dissipative_of_scaled traj Δt hΔt Ncut htail
  have hratioΔ :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (trajΔ n).P k ≤ M * (trajΔ n).D k := by
    simpa [trajΔ] using eventually_ratio_bound_of_scaled traj Δt hΔt M Ncut hratio
  have hDissΔ :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (trajΔ n) (lowShells (K_max := K_max) Ncut) ≤ C * E n := by
    simpa [trajΔ] using eventually_scaled_lowShell_dissipation_bound traj E Δt hΔt C Ncut hDiss_int
  exact
    eventual_discrete_gronwall_of_finite_source_closure_of_cutoff
      trajΔ E M C Ncut hM hMC hincΔ htailΔ hratioΔ hDissΔ

#check @eventual_discrete_gronwall_of_integrated_cutoff

/-- Barrier-specialized integrated version with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_integrated_barrier_fixed_cutoff {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Δt Φ ν M C : ℝ) (Ncut : ℕ)
    (hΔt : 0 ≤ Δt)
    (_hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (_hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max, (traj n).D k < (traj n).P k → Φ ≤ k4Cost ν k.val → False)
    (hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n ≤ Δt * shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut → (traj n).P k ≤ M * (traj n).D k)
    (hDiss_int :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          Δt * shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  exact
    eventual_discrete_gronwall_of_integrated_cutoff
      traj E Δt M C Ncut hΔt hM hMC
      hinc_int htail hratio hDiss_int

#check @eventual_discrete_gronwall_of_integrated_barrier_fixed_cutoff

end NSIntegratedHinc
