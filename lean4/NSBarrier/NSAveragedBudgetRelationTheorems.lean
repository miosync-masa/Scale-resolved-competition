import NSBarrier.NSShellwiseSumBoundTheorems
import NSBarrier.NSGalerkinCoeffProductRuleActual
import NSBarrier.NSGalerkinIntervalIntegralActual
import NSBarrier.NSIntegratedHinc
import Mathlib.Tactic

namespace NSAveragedBudgetRelationTheorems

open NSFiniteSource
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinIntervalIntegralActual
open NSGalerkinCoeffProductRuleActual

-- ============================================================
-- Averaged budget relation theorems
--
-- These expose the time-averaging and integration-budget
-- relations as named theorems rather than structure fields.
-- ============================================================

/-- [ODE] Integrated production equals Dt times the step average
    (from interval integral definition). -/
theorem Pint_eq_dt_mul_Pavg_of_interval_average
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      PintOfCont gid.time gid.PCont n k
        =
      gid.Δt * PavgOfCont gid.Δt gid.time gid.PCont n k :=
  hPint_eq_dt_mul_Pavg gid

/-- [ODE] Integrated dissipation equals Dt times the step average
    (from interval integral definition). -/
theorem Dint_eq_dt_mul_Davg_of_interval_average
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      DintOfCont gid.time gid.DCont n k
        =
      gid.Δt * DavgOfCont gid.Δt gid.time gid.DCont n k :=
  hDint_eq_dt_mul_Davg gid

/-- [ODE] Integrated shell net source equals Dt times instantaneous
    shell net source (from product-rule data). -/
theorem shellNetSource_integrated_eq_dt_mul_avg_of_interval_average
    {K_max : ℕ}
    (data : GalerkinIntegratedBudgetData K_max) :
    ∀ n : ℕ, ∀ S : Finset (Fin K_max),
      shellNetSource (data.intTraj n) S
        =
      data.Δt * shellNetSource (data.instTraj n) S :=
  shellNetSource_int_eq data

/-- [Alg] One-step enstrophy increment is bounded by the integrated
    shell net source (weakening equality to inequality). -/
theorem hinc_of_integrated_budget_of_interval_average
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Δt : ℝ) (hΔt : 0 ≤ Δt)
    (hinc_int :
      ∀ n : ℕ,
        E (n + 1) - E n ≤ Δt * shellNetSource (traj n) Finset.univ) :
    ∀ n : ℕ,
      E (n + 1) - E n
        ≤ shellNetSource (scaleBudgetTrajectory Δt hΔt traj n) Finset.univ :=
  hinc_of_integrated_shellNetSource traj E Δt hΔt hinc_int

#check @Pint_eq_dt_mul_Pavg_of_interval_average
#check @Dint_eq_dt_mul_Davg_of_interval_average
#check @shellNetSource_integrated_eq_dt_mul_avg_of_interval_average
#check @hinc_of_integrated_budget_of_interval_average

end NSAveragedBudgetRelationTheorems
