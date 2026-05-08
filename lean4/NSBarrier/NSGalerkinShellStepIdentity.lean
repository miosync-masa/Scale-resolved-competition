import NSBarrier.NSGalerkinEnstrophyIdentity
import Mathlib.Tactic

namespace NSGalerkinShellStepIdentity

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open scoped BigOperators

/-
  Goal of this file:
  package the last primitive Galerkin input

    Xi_{n+1,k} - Xi_{n,k} = P_int(n,k) - D_int(n,k)

  and automatically build:
  - total enstrophy trajectory
  - total exact integrated identity
  - the conditional discrete Grönwall consequences
-/

-- ============================================================
-- SECTION 1: CANONICAL TOTAL ENSTROPHY FROM SHELLWISE Xi
-- ============================================================

/-- Canonical total enstrophy trajectory obtained by summing shellwise enstrophy. -/
noncomputable def shellTotalEnstrophy {K_max : ℕ}
    (Xi : ℕ → Fin K_max → ℝ) : EnstrophyTrajectory :=
  fun n => ∑ k : Fin K_max, Xi n k

#check @shellTotalEnstrophy

/-- Primitive shellwise exact step-identity data for a Galerkin system. -/
structure GalerkinShellStepIdentityData (K_max : ℕ) where
  budgetData : GalerkinIntegratedBudgetData K_max
  Xi : ℕ → Fin K_max → ℝ

  /-- Exact shellwise integrated identity on each time slab. -/
  hstep_shell_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Xi (n + 1) k - Xi n k
        =
      (budgetData.intTraj n).P k - (budgetData.intTraj n).D k

#check @GalerkinShellStepIdentityData

theorem shellTotalEnstrophy_def
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy gid.Xi n = ∑ k : Fin K_max, gid.Xi n k := by
  intro n
  rfl

#check @shellTotalEnstrophy_def

-- ============================================================
-- SECTION 2: SHELLWISE EXACT STEP IDENTITY -> FINITE-DIMENSIONAL DATA
-- ============================================================

/-- Summing the shellwise exact identity gives the total exact integrated
Galerkin enstrophy identity. -/
theorem step_total_eq
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy gid.Xi (n + 1) - shellTotalEnstrophy gid.Xi n
        =
      shellNetSource (gid.budgetData.intTraj n) Finset.univ := by
  intro n
  simp only [shellTotalEnstrophy, shellNetSource, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => gid.hstep_shell_eq n k)

/-- The total exact identity implies the one-step integrated shell-budget inequality. -/
theorem hinc_gal_of_shellwise_step_identity
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy gid.Xi (n + 1) - shellTotalEnstrophy gid.Xi n
        ≤
      shellNetSource (gid.budgetData.intTraj n) Finset.univ := by
  intro n
  exact le_of_eq (step_total_eq gid n)

#check @step_total_eq
#check @hinc_gal_of_shellwise_step_identity

-- ============================================================
-- SECTION 3: BRIDGE TO NSGalerkinEnstrophyIdentity
-- ============================================================

/-- The primitive shellwise step-identity data induce the previous
`GalerkinEnstrophyIdentityData`. -/
noncomputable def toGalerkinEnstrophyIdentityData
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    GalerkinEnstrophyIdentityData K_max where
  budgetData := gid.budgetData
  E := shellTotalEnstrophy gid.Xi
  hstep_eq := step_total_eq gid

#check @toGalerkinEnstrophyIdentityData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the primitive shellwise exact Galerkin identity already yields the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_shellwise_step_identity_cutoff
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max)
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
          C * shellTotalEnstrophy gid.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy gid.Xi (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy gid.Xi N0 := by
  exact
    eventual_discrete_gronwall_of_galerkin_enstrophy_identity_cutoff
      (toGalerkinEnstrophyIdentityData gid)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

/-- Barrier-specialized version. -/
theorem eventual_discrete_gronwall_of_shellwise_step_identity_barrier_fixed_cutoff
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max)
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
          C * shellTotalEnstrophy gid.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy gid.Xi (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy gid.Xi N0 := by
  exact
    eventual_discrete_gronwall_of_galerkin_enstrophy_identity_barrier_fixed_cutoff
      (toGalerkinEnstrophyIdentityData gid)
      Φ ν M C Ncut
      hν hM hMC
      hbar htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_shellwise_step_identity_cutoff
#check @eventual_discrete_gronwall_of_shellwise_step_identity_barrier_fixed_cutoff

end NSGalerkinShellStepIdentity
