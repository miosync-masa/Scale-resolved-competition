import NSBarrier.NSGalerkinHinc
import Mathlib.Tactic

namespace NSGalerkinEnstrophyIdentity

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc

/-- Galerkin enstrophy-identity data.

This is the exact finite-dimensional ODE / integrated-shell-budget input:
on each time slab, the enstrophy increment is given exactly by the integrated
shell net source of the Galerkin system.

Thus the desired `hinc_gal` is immediate by weakening equality to inequality. -/
structure GalerkinEnstrophyIdentityData (K_max : ℕ) where
  budgetData : GalerkinIntegratedBudgetData K_max
  E : EnstrophyTrajectory

  /-- Exact integrated Galerkin enstrophy identity on each step. -/
  hstep_eq :
    ∀ n : ℕ,
      E (n + 1) - E n
        =
      shellNetSource (budgetData.intTraj n) Finset.univ

#check @GalerkinEnstrophyIdentityData

-- ============================================================
-- SECTION 1: EXACT IDENTITY -> INTEGRATED hinc_gal
-- ============================================================

/-- The exact Galerkin enstrophy identity immediately yields the integrated
one-step shell-budget inequality `hinc_gal`. -/
theorem hinc_gal_of_identity
    {K_max : ℕ}
    (gid : GalerkinEnstrophyIdentityData K_max) :
    ∀ n : ℕ,
      gid.E (n + 1) - gid.E n
        ≤
      shellNetSource (gid.budgetData.intTraj n) Finset.univ := by
  intro n
  exact le_of_eq (gid.hstep_eq n)

#check @hinc_gal_of_identity

/-- A low-shell integrated dissipation identity also yields the corresponding
inequality used downstream. -/
theorem hDiss_gal_of_identity
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Ncut : ℕ) (C : ℝ)
    (hDiss_eq :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut)
            =
          C * E n) :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut)
          ≤
        C * E n := by
  rcases hDiss_eq with ⟨Nd, hNd⟩
  refine ⟨Nd, ?_⟩
  intro n hn
  exact le_of_eq (hNd n hn)

#check @hDiss_gal_of_identity

-- ============================================================
-- SECTION 2: EXACT IDENTITY -> CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- Once the Galerkin step identity is known, the theorem
`eventual_discrete_gronwall_of_galerkin_integrated_cutoff`
applies directly. -/
theorem eventual_discrete_gronwall_of_galerkin_enstrophy_identity_cutoff
    {K_max : ℕ}
    (gid : GalerkinEnstrophyIdentityData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (gid.budgetData.instTraj n).P k ≤ (gid.budgetData.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (gid.budgetData.instTraj n).P k ≤ M * (gid.budgetData.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (gid.budgetData.intTraj n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * gid.E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, gid.E (N0 + m) ≤ (1 + M * C) ^ m * gid.E N0 := by
  exact
    eventual_discrete_gronwall_of_galerkin_integrated_cutoff
      gid.budgetData gid.E M C Ncut
      hM hMC
      (hinc_gal_of_identity gid)
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_galerkin_enstrophy_identity_cutoff

/-- Barrier-specialized version. -/
theorem eventual_discrete_gronwall_of_galerkin_enstrophy_identity_barrier_fixed_cutoff
    {K_max : ℕ}
    (gid : GalerkinEnstrophyIdentityData K_max)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max,
            (gid.budgetData.instTraj n).D k < (gid.budgetData.instTraj n).P k →
            Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (gid.budgetData.instTraj n).P k ≤ (gid.budgetData.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (gid.budgetData.instTraj n).P k ≤ M * (gid.budgetData.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (gid.budgetData.intTraj n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * gid.E n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, gid.E (N0 + m) ≤ (1 + M * C) ^ m * gid.E N0 := by
  exact
    eventual_discrete_gronwall_of_galerkin_integrated_barrier_fixed_cutoff
      gid.budgetData gid.E Φ ν M C Ncut
      hν hM hMC
      hbar
      (hinc_gal_of_identity gid)
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_galerkin_enstrophy_identity_barrier_fixed_cutoff

-- ============================================================
-- SECTION 3: A PACKAGED DATA STRUCTURE FOR THE FULL GALERKIN ROUTE
-- ============================================================

/-- Fully packaged Galerkin route:
exact step identity + low-shell dissipation bound + structural hypotheses. -/
structure FullGalerkinRouteData (K_max : ℕ) where
  gid : GalerkinEnstrophyIdentityData K_max
  M : ℝ
  C : ℝ
  Ncut : ℕ

  hM : 0 ≤ M
  hMC : 0 ≤ M * C

  htail :
    ∃ Nt : ℕ,
      ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max,
          Ncut ≤ k.val →
          (gid.budgetData.instTraj n).P k ≤ (gid.budgetData.instTraj n).D k

  hratio :
    ∃ Nr : ℕ,
      ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max,
          k.val < Ncut →
          (gid.budgetData.instTraj n).P k ≤ M * (gid.budgetData.instTraj n).D k

  hDiss_gal :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (gid.budgetData.intTraj n)
          (lowShells (K_max := K_max) Ncut)
            ≤
        C * gid.E n

#check @FullGalerkinRouteData

theorem eventual_discrete_gronwall_of_full_galerkin_route
    {K_max : ℕ}
    (data : FullGalerkinRouteData K_max) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, data.gid.E (N0 + m) ≤ (1 + data.M * data.C) ^ m * data.gid.E N0 := by
  exact
    eventual_discrete_gronwall_of_galerkin_enstrophy_identity_cutoff
      data.gid data.M data.C data.Ncut
      data.hM data.hMC
      data.htail data.hratio data.hDiss_gal

#check @eventual_discrete_gronwall_of_full_galerkin_route

end NSGalerkinEnstrophyIdentity
