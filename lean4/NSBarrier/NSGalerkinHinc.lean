import NSBarrier.NSIntegratedHinc
import Mathlib.Tactic

namespace NSGalerkinHinc

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc

/-- Galerkin integrated shell-budget data.

`instTraj n` is the instantaneous shell budget on the `n`-th time slab,
while `intTraj n` is the corresponding integrated shell budget over a time step
of length `Δt`.

The two are related by
  `P_int = Δt * P_inst`, `D_int = Δt * D_inst`.
-/
structure GalerkinIntegratedBudgetData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 ≤ Δt
  instTraj : BudgetTrajectory K_max
  intTraj : BudgetTrajectory K_max
  hP_int :
    ∀ n : ℕ, ∀ k : Fin K_max,
      (intTraj n).P k = Δt * (instTraj n).P k
  hD_int :
    ∀ n : ℕ, ∀ k : Fin K_max,
      (intTraj n).D k = Δt * (instTraj n).D k

#check @GalerkinIntegratedBudgetData

-- ============================================================
-- SECTION 1: INTEGRATED = Δt * INSTANTANEOUS
-- ============================================================

theorem shellNetSource_int_eq
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (n : ℕ) (S : Finset (Fin K_max)) :
    shellNetSource (data.intTraj n) S
      =
    data.Δt * shellNetSource (data.instTraj n) S := by
  unfold shellNetSource
  calc
    ∑ k ∈ S, ((data.intTraj n).P k - (data.intTraj n).D k)
      =
    ∑ k ∈ S, (data.Δt * (data.instTraj n).P k - data.Δt * (data.instTraj n).D k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [data.hP_int n k, data.hD_int n k]
    _ =
    ∑ k ∈ S, data.Δt * ((data.instTraj n).P k - (data.instTraj n).D k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    _ =
    data.Δt * ∑ k ∈ S, ((data.instTraj n).P k - (data.instTraj n).D k) := by
      rw [Finset.mul_sum]

theorem shellProductionSource_int_eq
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (n : ℕ) (S : Finset (Fin K_max)) :
    shellProductionSource (data.intTraj n) S
      =
    data.Δt * shellProductionSource (data.instTraj n) S := by
  unfold shellProductionSource
  calc
    ∑ k ∈ S, (data.intTraj n).P k
      =
    ∑ k ∈ S, data.Δt * (data.instTraj n).P k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [data.hP_int n k]
    _ =
    data.Δt * ∑ k ∈ S, (data.instTraj n).P k := by
      rw [Finset.mul_sum]

theorem shellDissipationSource_int_eq
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (n : ℕ) (S : Finset (Fin K_max)) :
    shellDissipationSource (data.intTraj n) S
      =
    data.Δt * shellDissipationSource (data.instTraj n) S := by
  unfold shellDissipationSource
  calc
    ∑ k ∈ S, (data.intTraj n).D k
      =
    ∑ k ∈ S, data.Δt * (data.instTraj n).D k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [data.hD_int n k]
    _ =
    data.Δt * ∑ k ∈ S, (data.instTraj n).D k := by
      rw [Finset.mul_sum]

#check @shellNetSource_int_eq
#check @shellProductionSource_int_eq
#check @shellDissipationSource_int_eq

-- ============================================================
-- SECTION 2: GALERKIN INTEGRATED BUDGET -> NSIntegratedHinc INPUTS
-- ============================================================

theorem hinc_int_of_galerkin_integrated_budget
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (E : EnstrophyTrajectory)
    (hinc_gal :
      ∀ n : ℕ,
        E (n + 1) - E n
          ≤
        shellNetSource (data.intTraj n) Finset.univ) :
    ∀ n : ℕ,
      E (n + 1) - E n
        ≤
      data.Δt * shellNetSource (data.instTraj n) Finset.univ := by
  intro n
  simpa [shellNetSource_int_eq] using hinc_gal n

theorem hDiss_int_of_galerkin_integrated_budget
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (E : EnstrophyTrajectory)
    (C : ℝ) (Ncut : ℕ)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (data.intTraj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        data.Δt * shellDissipationSource (data.instTraj n) (lowShells (K_max := K_max) Ncut)
          ≤ C * E n := by
  rcases hDiss_gal with ⟨Nd, hNd⟩
  refine ⟨Nd, ?_⟩
  intro n hn
  simpa [shellDissipationSource_int_eq] using hNd n hn

#check @hinc_int_of_galerkin_integrated_budget
#check @hDiss_int_of_galerkin_integrated_budget

-- ============================================================
-- SECTION 3: GALERKIN INTEGRATED BUDGET -> CONDITIONAL DISCRETE GRONWALL
-- ============================================================

theorem eventual_discrete_gronwall_of_galerkin_integrated_cutoff
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (E : EnstrophyTrajectory)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hinc_gal :
      ∀ n : ℕ,
        E (n + 1) - E n
          ≤
        shellNetSource (data.intTraj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (data.instTraj n).P k ≤ (data.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut →
            (data.instTraj n).P k ≤ M * (data.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (data.intTraj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  have hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n
          ≤
        data.Δt * shellNetSource (data.instTraj n) Finset.univ :=
    hinc_int_of_galerkin_integrated_budget data E hinc_gal
  have hDiss_int :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          data.Δt * shellDissipationSource (data.instTraj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n :=
    hDiss_int_of_galerkin_integrated_budget data E C Ncut hDiss_gal
  exact
    eventual_discrete_gronwall_of_integrated_cutoff
      data.instTraj E data.Δt M C Ncut
      data.hΔt hM hMC
      hinc_int htail hratio hDiss_int

#check @eventual_discrete_gronwall_of_galerkin_integrated_cutoff

/-- Barrier-specialized integrated Galerkin version with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_galerkin_integrated_barrier_fixed_cutoff
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max)
    (E : EnstrophyTrajectory)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max,
            (data.instTraj n).D k < (data.instTraj n).P k →
            Φ ≤ k4Cost ν k.val → False)
    (hinc_gal :
      ∀ n : ℕ,
        E (n + 1) - E n
          ≤
        shellNetSource (data.intTraj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (data.instTraj n).P k ≤ (data.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max, k.val < Ncut →
            (data.instTraj n).P k ≤ M * (data.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (data.intTraj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  have hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n
          ≤
        data.Δt * shellNetSource (data.instTraj n) Finset.univ :=
    hinc_int_of_galerkin_integrated_budget data E hinc_gal
  have hDiss_int :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          data.Δt * shellDissipationSource (data.instTraj n) (lowShells (K_max := K_max) Ncut)
            ≤ C * E n :=
    hDiss_int_of_galerkin_integrated_budget data E C Ncut hDiss_gal
  exact
    eventual_discrete_gronwall_of_integrated_barrier_fixed_cutoff
      data.instTraj E data.Δt Φ ν M C Ncut
      data.hΔt hν hM hMC
      hbar hinc_int htail hratio hDiss_int

#check @eventual_discrete_gronwall_of_galerkin_integrated_barrier_fixed_cutoff

end NSGalerkinHinc
