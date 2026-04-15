import NSBarrier.NSGalerkinCoeffProductRuleActual
import NSBarrier.NSTorusShellActual
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open NSTorusShellActual
open MeasureTheory
open scoped BigOperators

namespace NSGalerkinCoeffODEProductRuleProof

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

/-
  Final actual product-rule layer.

  We work with a real-coordinate version of the finite-dimensional Galerkin
  coefficient system.  The shellwise enstrophy is defined as a weighted sum
  of coefficient squares over the shell block.  The coefficient ODE is split into

      a'_κ = N_κ - ν_κ a_κ

  and the shellwise production / dissipation are defined accordingly:

      P_k = Σ_{κ in shell k} 2 w_κ a_κ N_κ
      D_k = Σ_{κ in shell k} 2 w_κ ν_κ a_κ^2

  The key theorem of this file is:

      HasDerivAt XiCont_k (PCont_k - DCont_k) t

  which is the last analytic ingredient needed by
  `NSGalerkinCoeffProductRuleActual`.
-/

-- ============================================================
-- SECTION 1: ACTUAL MODEWISE DEFINITIONS
-- ============================================================

/-- Shellwise enstrophy from actual Galerkin coefficients. -/
noncomputable def XiContOfCoeffs
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellOf : Mode → Fin K_max)
    (weight : Mode → ℝ)
    (coeff : ℝ → Mode → ℝ)
    (t : ℝ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k), weight κ * (coeff t κ)^2

/-- Shellwise production from actual Galerkin coefficients and nonlinear term. -/
noncomputable def PContOfCoeffs
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellOf : Mode → Fin K_max)
    (weight : Mode → ℝ)
    (coeff : ℝ → Mode → ℝ)
    (nonlin : ℝ → Mode → ℝ)
    (t : ℝ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k),
    2 * weight κ * coeff t κ * nonlin t κ

/-- Shellwise dissipation from actual Galerkin coefficients and linear damping term. -/
noncomputable def DContOfCoeffs
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellOf : Mode → Fin K_max)
    (weight : Mode → ℝ)
    (coeff : ℝ → Mode → ℝ)
    (damp : Mode → ℝ)
    (t : ℝ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k),
    2 * weight κ * damp κ * (coeff t κ)^2

#check @XiContOfCoeffs
#check @PContOfCoeffs
#check @DContOfCoeffs

-- ============================================================
-- SECTION 2: ACTUAL COEFFICIENT ODE DATA
-- ============================================================

/-- Actual finite-dimensional Galerkin coefficient ODE data.

`coeffDeriv` is the derivative of the real-coordinate Galerkin coefficient,
and the ODE is split as

    coeffDeriv = nonlin - damp * coeff.

The remaining fields are exactly the ones already expected by
`GalerkinCoeffProductRuleData`, except that `XiCont`, `PCont`, `DCont`
are now defined from the coefficients and the ODE.
-/
structure GalerkinCoeffODEProductRuleProofData (K_max : ℕ) where
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
  coeffDeriv : ℝ → Mode → ℝ
  nonlin : ℝ → Mode → ℝ

  /-- Step averages, kept explicit to connect with the downstream chain. -/
  Pavg : ℕ → Fin K_max → ℝ
  Davg : ℕ → Fin K_max → ℝ
  hDavg_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Davg n k

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

  /-- The chosen step averages really are interval averages. -/
  hPavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Pavg n k =
        (∫ t in time n..time (n + 1),
          PContOfCoeffs modes shellOf weight coeff nonlin t k) / Δt

  hDavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Davg n k =
        (∫ t in time n..time (n + 1),
          DContOfCoeffs modes shellOf weight coeff damp t k) / Δt

  /-- Coefficient differentiability. -/
  hcoeff_hasDeriv :
    ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt (fun s => coeff s κ) (coeffDeriv t κ) t

  /-- Actual finite-dimensional ODE:
      coeffDeriv = nonlin - damp * coeff. -/
  hcoeff_ode :
    ∀ κ : Mode, ∀ t : ℝ,
      coeffDeriv t κ = nonlin t κ - damp κ * coeff t κ

#check @GalerkinCoeffODEProductRuleProofData

-- ============================================================
-- SECTION 3: PRODUCT RULE ON A SINGLE MODE
-- ============================================================

theorem hasDerivAt_weighted_coeff_sq
    {K_max : ℕ}
    (d : GalerkinCoeffODEProductRuleProofData K_max)
    (κ : Mode) (t : ℝ) :
    HasDerivAt
      (fun s => d.weight κ * (d.coeff s κ)^2)
      (2 * d.weight κ * d.coeff t κ * d.nonlin t κ
        - 2 * d.weight κ * d.damp κ * (d.coeff t κ)^2)
      t := by
  have hc : HasDerivAt (fun s => d.coeff s κ) (d.coeffDeriv t κ) t :=
    d.hcoeff_hasDeriv κ t
  have hsq :
      HasDerivAt
        (fun s => d.coeff s κ * d.coeff s κ)
        (d.coeffDeriv t κ * d.coeff t κ + d.coeff t κ * d.coeffDeriv t κ)
        t := by
    simpa using hc.mul hc
  have hconst :
      HasDerivAt
        (fun s => d.weight κ * (d.coeff s κ * d.coeff s κ))
        (d.weight κ *
          (d.coeffDeriv t κ * d.coeff t κ + d.coeff t κ * d.coeffDeriv t κ))
        t := by
    simpa using hsq.const_mul (d.weight κ)
  convert hconst using 1
  · funext s
    ring
  · rw [d.hcoeff_ode κ t]
    ring

#check @hasDerivAt_weighted_coeff_sq

-- ============================================================
-- SECTION 4: PRODUCT RULE ON A WHOLE SHELL
-- ============================================================

theorem hXi_hasDeriv_of_coeffODE
    {K_max : ℕ}
    (d : GalerkinCoeffODEProductRuleProofData K_max) :
    ∀ k : Fin K_max, ∀ t : ℝ,
      HasDerivAt
        (fun s => XiContOfCoeffs d.modes d.shellOf d.weight d.coeff s k)
        (PContOfCoeffs d.modes d.shellOf d.weight d.coeff d.nonlin t k
          - DContOfCoeffs d.modes d.shellOf d.weight d.coeff d.damp t k)
        t := by
  intro k t
  let S : Finset Mode := d.modes.filter (fun κ => d.shellOf κ = k)
  have hsum :
      HasDerivAt
        (fun s => ∑ κ ∈ S, d.weight κ * (d.coeff s κ)^2)
        (∑ κ ∈ S,
          (2 * d.weight κ * d.coeff t κ * d.nonlin t κ
            - 2 * d.weight κ * d.damp κ * (d.coeff t κ)^2))
        t := by
    classical
    unfold S
    refine Finset.induction_on (d.modes.filter fun κ => d.shellOf κ = k) ?base ?step
    · simpa using (hasDerivAt_const t (0 : ℝ))
    · intro a S haS ih
      have ha :
          HasDerivAt
            (fun s => d.weight a * (d.coeff s a)^2)
            (2 * d.weight a * d.coeff t a * d.nonlin t a
              - 2 * d.weight a * d.damp a * (d.coeff t a)^2)
            t :=
        hasDerivAt_weighted_coeff_sq d a t
      have hadd := ha.add ih
      have : HasDerivAt
            (fun s => d.weight a * (d.coeff s a)^2 + ∑ κ ∈ S, d.weight κ * (d.coeff s κ)^2)
            ((2 * d.weight a * d.coeff t a * d.nonlin t a
              - 2 * d.weight a * d.damp a * (d.coeff t a)^2)
            + (∑ x ∈ S, (2 * d.weight x * d.coeff t x * d.nonlin t x
              - 2 * d.weight x * d.damp x * (d.coeff t x)^2)))
            t := hadd
      simp only [Finset.sum_insert haS]
      convert this using 1
  have hsum_rewrite :
      (∑ κ ∈ S,
        (2 * d.weight κ * d.coeff t κ * d.nonlin t κ
          - 2 * d.weight κ * d.damp κ * (d.coeff t κ)^2))
        =
      PContOfCoeffs d.modes d.shellOf d.weight d.coeff d.nonlin t k
        - DContOfCoeffs d.modes d.shellOf d.weight d.coeff d.damp t k := by
    unfold PContOfCoeffs DContOfCoeffs S
    rw [Finset.sum_sub_distrib]
  simpa [XiContOfCoeffs, S, hsum_rewrite] using hsum

#check @hXi_hasDeriv_of_coeffODE

-- ============================================================
-- SECTION 5: BRIDGE TO NSGalerkinCoeffProductRuleActual
-- ============================================================

/-- The actual coefficient ODE data induce the previous
`GalerkinCoeffProductRuleData`. -/
noncomputable def toGalerkinCoeffProductRuleData
    {K_max : ℕ}
    (d : GalerkinCoeffODEProductRuleProofData K_max) :
    GalerkinCoeffProductRuleData K_max where
  Δt := d.Δt
  hΔt := d.hΔt
  XiCont := XiContOfCoeffs d.modes d.shellOf d.weight d.coeff
  PCont := PContOfCoeffs d.modes d.shellOf d.weight d.coeff d.nonlin
  DCont := DContOfCoeffs d.modes d.shellOf d.weight d.coeff d.damp
  time := d.time
  htime_zero := d.htime_zero
  htime_succ := d.htime_succ
  Pavg := d.Pavg
  Davg := d.Davg
  hDavg_nonneg := d.hDavg_nonneg
  hPavg_eq := d.hPavg_eq
  hDavg_eq := d.hDavg_eq
  hPCont_intervalIntegrable := d.hPCont_intervalIntegrable
  hDCont_intervalIntegrable := d.hDCont_intervalIntegrable
  hXi_hasDeriv := hXi_hasDeriv_of_coeffODE d

#check @toGalerkinCoeffProductRuleData

-- ============================================================
-- SECTION 6: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the actual Galerkin coefficient ODE already yields the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_coeffODE_cutoff
    {K_max : ℕ}
    (d : GalerkinCoeffODEProductRuleProofData K_max)
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
                      (toGalerkinCoeffProductRuleData d))))) n).P k
              ≤
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData d))))) n).D k)
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
                      (toGalerkinCoeffProductRuleData d))))) n).P k
              ≤
            M * (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData d))))) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData d))))) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C *
            shellTotalEnstrophy
              (XiDiscrete
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData
                      (toGalerkinCoeffProductRuleData d))))) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy
          (XiDiscrete
            (toGalerkinCoeffODEContData
              (toGalerkinCoeffIntegratedProofData
                (toGalerkinIntervalIntegralActualData
                  (toGalerkinCoeffProductRuleData d))))) (N0 + m)
          ≤
        (1 + M * C) ^ m *
          shellTotalEnstrophy
            (XiDiscrete
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData
                    (toGalerkinCoeffProductRuleData d))))) N0 := by
  exact
    eventual_discrete_gronwall_of_productRule_cutoff
      (toGalerkinCoeffProductRuleData d)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_coeffODE_cutoff

end NSGalerkinCoeffODEProductRuleProof
