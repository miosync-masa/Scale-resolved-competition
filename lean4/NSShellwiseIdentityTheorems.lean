import NSBarrier.NSProjectorShellEqualityTheorems
import NSBarrier.NSGalerkinShellStepIdentity
import NSBarrier.NSGalerkinEnstrophyIdentity
import Mathlib.Tactic

namespace NSShellwiseIdentityTheorems

open NSFiniteSource
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open NSGalerkinShellStepIdentity

-- ============================================================
-- Shellwise identity theorems
--
-- These are the top-level identity theorems that bundle the
-- modewise -> shellwise -> averaged -> identity chain.
-- ============================================================

/-- [Alg] Shellwise exact step identity:
    Xi(n+1, k) - Xi(n, k) = P_int(n, k) - D_int(n, k).

    This is the fundamental shellwise enstrophy balance,
    derived from the Galerkin coefficient ODE via product rule
    and FTC integration. -/
theorem shellwise_step_identity_of_definition
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      gid.Xi (n + 1) k - gid.Xi n k
        =
      (gid.budgetData.intTraj n).P k - (gid.budgetData.intTraj n).D k :=
  gid.hstep_shell_eq

/-- [Alg] Total enstrophy step identity:
    E(n+1) - E(n) = shellNetSource(intTraj(n), univ).

    Obtained by summing the shellwise identity over all shells. -/
theorem shellwise_step_identity_integrated_of_definition
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy gid.Xi (n + 1) - shellTotalEnstrophy gid.Xi n
        =
      shellNetSource (gid.budgetData.intTraj n) Finset.univ :=
  step_total_eq gid

/-- [Alg] Shell net source decomposes as production minus dissipation.
    This is definitional from shellNetSource. -/
theorem shellwise_net_eq_prod_minus_diss_of_definition
    {K_max : ℕ}
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) :
    shellNetSource sb S = S.sum (fun k => sb.P k - sb.D k) := by
  rfl

/-- [Alg] The total enstrophy identity implies the one-step hinc inequality
    (weakening equality to inequality). -/
theorem hinc_of_shellwise_step_identity_of_definition
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy gid.Xi (n + 1) - shellTotalEnstrophy gid.Xi n
        ≤
      shellNetSource (gid.budgetData.intTraj n) Finset.univ :=
  hinc_gal_of_shellwise_step_identity gid

/-- [Alg] Therefore the shellwise identity chain yields the conditional
    discrete Gronwall bound with a fixed cutoff.

    This is the **master theorem** that bundles:
    - modewise majorization
    - shellwise sum bounds
    - averaged budget relations
    - projector shell equalities
    - shellwise identities
    into a single exponential enstrophy bound. -/
theorem eventual_discrete_gronwall_of_shellwise_identity_of_definition
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M) (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ, ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, Ncut ≤ k.val →
          (gid.budgetData.instTraj n).P k
            ≤ (gid.budgetData.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ, ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (gid.budgetData.instTraj n).P k
            ≤ M * (gid.budgetData.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (gid.budgetData.intTraj n)
          (lowShells (K_max := K_max) Ncut)
          ≤
        C * shellTotalEnstrophy gid.Xi n) :
    ∃ N0 : ℕ, ∀ m : ℕ,
      shellTotalEnstrophy gid.Xi (N0 + m)
        ≤
      (1 + M * C) ^ m * shellTotalEnstrophy gid.Xi N0 :=
  eventual_discrete_gronwall_of_shellwise_step_identity_cutoff
    gid M C Ncut hM hMC htail hratio hDiss_gal

#check @shellwise_step_identity_of_definition
#check @shellwise_step_identity_integrated_of_definition
#check @shellwise_net_eq_prod_minus_diss_of_definition
#check @hinc_of_shellwise_step_identity_of_definition
#check @eventual_discrete_gronwall_of_shellwise_identity_of_definition

end NSShellwiseIdentityTheorems
