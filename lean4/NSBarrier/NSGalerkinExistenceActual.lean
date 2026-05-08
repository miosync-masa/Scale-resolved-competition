import NSBarrier.NSGalerkinCoeffConcreteActual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open MeasureTheory
open NSTorusShellActual

namespace NSGalerkinExistenceActual

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
open NSGalerkinCoeffConcreteActual

/-
  Final finite-dimensional insertion layer.

  We realize the Galerkin state space concretely as `Fin m → ℝ`.
  Each Fourier mode κ is assigned a coordinate `coordOf κ : Fin m`,
  and the actual Galerkin coefficient is read off as
    coeff(t, κ) = state(t, coordOf κ).

  The only remaining analytic input is then:
    HasDerivAt (fun s => state s i) (rhsCoord t i) t
  for each coordinate `i`, together with the identification of the modewise RHS:
    rhsCoord t (coordOf κ) = nonlin t κ - damp κ * coeff t κ.
-/

-- ============================================================
-- SECTION 1: CONCRETE FINITE-DIMENSIONAL STATE SPACE
-- ============================================================

/-- Actual finite-dimensional Galerkin state data on the concrete
state space `Fin m → ℝ`. -/
structure ActualFiniteDimensionalGalerkinStateData (K_max m : ℕ) where
  Δt : ℝ
  hΔt : 0 < Δt

  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  modes : Finset Mode
  shellOf : Mode → Fin K_max
  coordOf : Mode → Fin m
  weight : Mode → ℝ
  damp : Mode → ℝ

  /-- Concrete finite-dimensional Galerkin state and its
  coordinatewise RHS. -/
  state : ℝ → Fin m → ℝ
  rhsCoord : ℝ → Fin m → ℝ

  /-- Modewise nonlinear term, already interpreted on the
  concrete state. -/
  nonlin : ℝ → Mode → ℝ

  /-- Step averages used by the downstream chain. -/
  Pavg : ℕ → Fin K_max → ℝ
  Davg : ℕ → Fin K_max → ℝ
  hDavg_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Davg n k

  /-- Interval-integrability of the induced shellwise
  production/dissipation. -/
  hPCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => PContOfCoeffs modes shellOf weight
          (fun s κ => state s (coordOf κ)) nonlin t k)
        volume (time n) (time (n + 1))

  hDCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => DContOfCoeffs modes shellOf weight
          (fun s κ => state s (coordOf κ)) damp t k)
        volume (time n) (time (n + 1))

  /-- The chosen step averages really are interval averages. -/
  hPavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Pavg n k =
        (∫ t in time n..time (n + 1),
          PContOfCoeffs modes shellOf weight
            (fun s κ => state s (coordOf κ)) nonlin t k) / Δt

  hDavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Davg n k =
        (∫ t in time n..time (n + 1),
          DContOfCoeffs modes shellOf weight
            (fun s κ => state s (coordOf κ)) damp t k) / Δt

  /-- Coordinatewise differentiability of the concrete
  finite-dimensional ODE solution. -/
  hstate_hasDeriv :
    ∀ i : Fin m, ∀ t : ℝ,
      HasDerivAt (fun s => state s i) (rhsCoord t i) t

  /-- Identification of the modewise RHS from the
  coordinate RHS. -/
  hrhs_mode :
    ∀ κ : Mode, ∀ t : ℝ,
      rhsCoord t (coordOf κ) =
        nonlin t κ - damp κ * state t (coordOf κ)

#check @ActualFiniteDimensionalGalerkinStateData

/-- The actual Galerkin coefficient read off from the
concrete state. -/
noncomputable def coeffOfState
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ℝ → Mode → ℝ :=
  fun t κ => d.state t (d.coordOf κ)

#check @coeffOfState

theorem hcoeff_solution_of_state
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt (fun s => coeffOfState d s κ)
        (d.nonlin t κ - d.damp κ * coeffOfState d t κ)
        t := by
  intro κ t
  simpa [coeffOfState, d.hrhs_mode κ t] using
    d.hstate_hasDeriv (d.coordOf κ) t

#check @hcoeff_solution_of_state

-- ============================================================
-- SECTION 2: BRIDGE TO THE FINAL CONCRETE ACTUAL DATA
-- ============================================================

noncomputable def toActualGalerkinCoeffSolutionData
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ActualGalerkinCoeffSolutionData K_max where
  Δt := d.Δt
  hΔt := d.hΔt
  time := d.time
  htime_zero := d.htime_zero
  htime_succ := d.htime_succ
  modes := d.modes
  shellOf := d.shellOf
  weight := d.weight
  damp := d.damp
  coeff := coeffOfState d
  nonlin := d.nonlin
  hPCont_intervalIntegrable := d.hPCont_intervalIntegrable
  hDCont_intervalIntegrable := d.hDCont_intervalIntegrable
  hDavg_nonneg := by
    intro n k
    unfold DavgOfCont DintOfCont coeffOfState
    rw [show (fun t => DContOfCoeffs d.modes d.shellOf d.weight
        (fun s κ => d.state s (d.coordOf κ)) d.damp t k)
      = (fun t => DContOfCoeffs d.modes d.shellOf d.weight
        (fun s κ => d.state s (d.coordOf κ)) d.damp t k) from rfl]
    rw [← d.hDavg_eq n k]
    exact d.hDavg_nonneg n k
  hcoeff_solution := hcoeff_solution_of_state d

#check @toActualGalerkinCoeffSolutionData

-- ============================================================
-- SECTION 3: FINAL CONSEQUENCES
-- ============================================================

theorem eventual_discrete_gronwall_of_finiteDimensionalState_cutoff
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ, ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, Ncut ≤ k.val →
          (instBudgetTrajectory
            (toGalerkinODEStepData
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData
                        (toActualGalerkinCoeffSolutionData d)))))))
            n).P k
            ≤
          (instBudgetTrajectory
            (toGalerkinODEStepData
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData
                        (toActualGalerkinCoeffSolutionData d)))))))
            n).D k)
    (hratio :
      ∃ Nr : ℕ, ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (instBudgetTrajectory
            (toGalerkinODEStepData
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData
                        (toActualGalerkinCoeffSolutionData d)))))))
            n).P k
            ≤
          M *
          (instBudgetTrajectory
            (toGalerkinODEStepData
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData
                        (toActualGalerkinCoeffSolutionData d)))))))
            n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource
          (intBudgetTrajectory
            (toGalerkinODEStepData
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData
                      (toGalerkinCoeffODEProductRuleProofData
                        (toActualGalerkinCoeffSolutionData d)))))))
            n)
          (lowShells (K_max := K_max) Ncut)
          ≤
        C *
        shellTotalEnstrophy
          (XiDiscrete
            (toGalerkinCoeffODEContData
              (toGalerkinCoeffIntegratedProofData
                (toGalerkinIntervalIntegralActualData
                  (toGalerkinCoeffProductRuleData
                    (toGalerkinCoeffODEProductRuleProofData
                      (toActualGalerkinCoeffSolutionData d)))))))
          n) :
    ∃ N0 : ℕ, ∀ m : ℕ,
      shellTotalEnstrophy
        (XiDiscrete
          (toGalerkinCoeffODEContData
            (toGalerkinCoeffIntegratedProofData
              (toGalerkinIntervalIntegralActualData
                (toGalerkinCoeffProductRuleData
                  (toGalerkinCoeffODEProductRuleProofData
                    (toActualGalerkinCoeffSolutionData d)))))))
        (N0 + m)
        ≤
      (1 + M * C) ^ m *
      shellTotalEnstrophy
        (XiDiscrete
          (toGalerkinCoeffODEContData
            (toGalerkinCoeffIntegratedProofData
              (toGalerkinIntervalIntegralActualData
                (toGalerkinCoeffProductRuleData
                  (toGalerkinCoeffODEProductRuleProofData
                    (toActualGalerkinCoeffSolutionData d)))))))
        N0 := by
  exact
    eventual_discrete_gronwall_of_actual_coeff_solution_cutoff
      (toActualGalerkinCoeffSolutionData d)
      M C Ncut hM hMC htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_finiteDimensionalState_cutoff

end NSGalerkinExistenceActual
