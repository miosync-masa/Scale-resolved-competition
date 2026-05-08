import NSBarrier.NSGalerkinCoeffODEProductRuleProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open MeasureTheory
open NSTorusShellActual

namespace NSGalerkinCoeffConcreteActual

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open NSGalerkinShellStepIdentity
open NSGalerkinODEActual
open NSGalerkinCoeffODEActual
open NSGalerkinCoeffIntegratedProof
open NSGalerkinIntervalIntegralActual
open NSGalerkinCoeffProductRuleActual
open NSGalerkinCoeffODEProductRuleProof

/-
  This is the final thin "actual insertion" layer.

  We do not introduce an extra `coeffDeriv` field.
  Instead, we take the actual Galerkin coefficient ODE directly as

      d/dt coeff(t,κ) = nonlin(t,κ) - damp(κ) * coeff(t,κ),

  and use that to supply `hcoeff_hasDeriv` and `hcoeff_ode`
  required by `NSGalerkinCoeffODEProductRuleProofData`.
-/

-- ============================================================
-- SECTION 1: ACTUAL COEFFICIENT-ODE SOLUTION DATA
-- ============================================================

structure ActualGalerkinCoeffSolutionData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 < Δt

  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  modes : Finset Mode
  shellOf : Mode → Fin K_max

  weight : Mode → ℝ
  damp : Mode → ℝ

  coeff : ℝ → Mode → ℝ
  nonlin : ℝ → Mode → ℝ

  /-- Interval-integrability of the induced shellwise production/dissipation. -/
  hPCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => PContOfCoeffs modes shellOf weight coeff nonlin t k)
        volume (time n) (time (n + 1))

  hDCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => DContOfCoeffs modes shellOf weight coeff damp t k)
        volume (time n) (time (n + 1))

  /-- Nonnegativity of the canonical averaged dissipation. -/
  hDavg_nonneg :
    ∀ n : ℕ, ∀ k : Fin K_max,
      0 ≤ DavgOfCont Δt time (DContOfCoeffs modes shellOf weight coeff damp) n k

  /-- The actual coefficient ODE solution property. -/
  hcoeff_solution :
    ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt
        (fun s => coeff s κ)
        (nonlin t κ - damp κ * coeff t κ)
        t

#check @ActualGalerkinCoeffSolutionData

theorem hcoeff_hasDeriv_of_actual_solution
    {K_max : ℕ}
    (d : ActualGalerkinCoeffSolutionData K_max) :
    ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt
        (fun s => d.coeff s κ)
        (d.nonlin t κ - d.damp κ * d.coeff t κ)
        t := by
  intro κ t
  exact d.hcoeff_solution κ t

#check @hcoeff_hasDeriv_of_actual_solution

-- ============================================================
-- SECTION 2: BRIDGE TO THE PRODUCT-RULE PROOF DATA
-- ============================================================

noncomputable def toGalerkinCoeffODEProductRuleProofData
    {K_max : ℕ}
    (d : ActualGalerkinCoeffSolutionData K_max) :
    GalerkinCoeffODEProductRuleProofData K_max where
  Δt := d.Δt
  hΔt := d.hΔt

  time := d.time
  htime_zero := d.htime_zero
  htime_succ := d.htime_succ

  modes := d.modes
  shellOf := d.shellOf

  weight := d.weight
  damp := d.damp

  coeff := d.coeff
  coeffDeriv := fun t κ => d.nonlin t κ - d.damp κ * d.coeff t κ
  nonlin := d.nonlin

  Pavg := PavgOfCont d.Δt d.time (PContOfCoeffs d.modes d.shellOf d.weight d.coeff d.nonlin)
  Davg := DavgOfCont d.Δt d.time (DContOfCoeffs d.modes d.shellOf d.weight d.coeff d.damp)
  hDavg_nonneg := d.hDavg_nonneg

  hPCont_intervalIntegrable := d.hPCont_intervalIntegrable
  hDCont_intervalIntegrable := d.hDCont_intervalIntegrable

  hPavg_eq := by
    intro n k
    rfl

  hDavg_eq := by
    intro n k
    rfl

  hcoeff_hasDeriv := by
    intro κ t
    simpa using hcoeff_hasDeriv_of_actual_solution d κ t

  hcoeff_ode := by
    intro κ t
    rfl

#check @toGalerkinCoeffODEProductRuleProofData

-- ============================================================
-- SECTION 3: FINAL CONSEQUENCES
-- ============================================================

theorem eventual_discrete_gronwall_of_actual_coeff_solution_cutoff
    {K_max : ℕ}
    (d : ActualGalerkinCoeffSolutionData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n).P k
              ≤
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n).P k
              ≤
            M * (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C *
            shellTotalEnstrophy
              (XiDiscrete
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData
                        (toGalerkinCoeffODEProductRuleProofData d)))))) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy
          (XiDiscrete
            (toGalerkinCoeffODEContData
              (toGalerkinCoeffIntegratedProofData
                (toGalerkinIntervalIntegralActualData
                  (toGalerkinCoeffProductRuleData
                    (toGalerkinCoeffODEProductRuleProofData d)))))) (N0 + m)
          ≤
        (1 + M * C) ^ m *
          shellTotalEnstrophy
            (XiDiscrete
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData d)))))) N0 := by
  exact
    eventual_discrete_gronwall_of_coeffODE_cutoff
      (toGalerkinCoeffODEProductRuleProofData d)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_actual_coeff_solution_cutoff

end NSGalerkinCoeffConcreteActual
