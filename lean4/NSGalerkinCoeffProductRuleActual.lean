import NSBarrier.NSGalerkinIntervalIntegralActual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open MeasureTheory

namespace NSGalerkinCoeffProductRuleActual

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

/-
  Final analytic reduction:

    d/dt XiCont(t,k) = PCont(t,k) - DCont(t,k)
      ==> by FTC
    XiCont(t_{n+1},k) - XiCont(t_n,k)
        = ∫_{t_n}^{t_{n+1}} (PCont(t,k) - DCont(t,k)) dt

  This file packages exactly that bridge.
-/

-- ============================================================
-- SECTION 1: PRODUCT-RULE / DERIVATIVE DATA
-- ============================================================

/-- Final product-rule data for the continuous-time Galerkin coefficient system. -/
structure GalerkinCoeffProductRuleData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 < Δt

  XiCont : ℝ → Fin K_max → ℝ
  PCont : ℝ → Fin K_max → ℝ
  DCont : ℝ → Fin K_max → ℝ

  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  /-- Step averages, kept explicit because the downstream chain already uses them. -/
  Pavg : ℕ → Fin K_max → ℝ
  Davg : ℕ → Fin K_max → ℝ
  hDavg_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Davg n k

  /-- `Pavg` and `Davg` are the interval averages of `PCont` and `DCont`. -/
  hPavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Pavg n k = (∫ t in time n..time (n + 1), PCont t k) / Δt

  hDavg_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Davg n k = (∫ t in time n..time (n + 1), DCont t k) / Δt

  /-- Interval integrability of the shellwise production and dissipation. -/
  hPCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable (fun t => PCont t k) volume (time n) (time (n + 1))

  hDCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable (fun t => DCont t k) volume (time n) (time (n + 1))

  /-- Final product-rule identity:
      the shellwise enstrophy derivative equals production minus dissipation. -/
  hXi_hasDeriv :
    ∀ k : Fin K_max, ∀ t : ℝ,
      HasDerivAt (fun s => XiCont s k) (PCont t k - DCont t k) t

#check @GalerkinCoeffProductRuleData

-- ============================================================
-- SECTION 2: FTC -> INTEGRATED SHELL IDENTITY
-- ============================================================

/-- The derivative identity implies the exact interval-integrated shell identity.

Depending on the local Mathlib version, the FTC lemma used in the last line may be
named one of:
- `intervalIntegral.integral_eq_sub_of_hasDeriv_right`
- `intervalIntegral.integral_deriv_eq_sub`
- `intervalIntegral.integral_deriv_eq_sub'`

The proof shape is the same in all cases. -/
theorem hXi_interval_eq_of_productRule
    {K_max : ℕ}
    (gid : GalerkinCoeffProductRuleData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      gid.XiCont (gid.time (n + 1)) k - gid.XiCont (gid.time n) k
        =
      ∫ t in gid.time n..gid.time (n + 1), (gid.PCont t k - gid.DCont t k) := by
  intro n k
  have hInt :
      IntervalIntegrable (fun t => gid.PCont t k - gid.DCont t k)
        volume (gid.time n) (gid.time (n + 1)) :=
    (gid.hPCont_intervalIntegrable n k).sub (gid.hDCont_intervalIntegrable n k)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => gid.XiCont s k)
      (f' := fun t => gid.PCont t k - gid.DCont t k)
      (fun x _ => gid.hXi_hasDeriv k x)
      hInt
  linarith

#check @hXi_interval_eq_of_productRule

/-- Integrated production equals `Δt` times the chosen step average. -/
theorem hPint_eq_of_Pavg
    {K_max : ℕ}
    (gid : GalerkinCoeffProductRuleData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      PintOfCont gid.time gid.PCont n k
        =
      gid.Δt * gid.Pavg n k := by
  intro n k
  rw [gid.hPavg_eq n k]
  unfold PintOfCont
  have hΔt0 : gid.Δt ≠ 0 := ne_of_gt gid.hΔt
  field_simp [hΔt0]

/-- Integrated dissipation equals `Δt` times the chosen step average. -/
theorem hDint_eq_of_Davg
    {K_max : ℕ}
    (gid : GalerkinCoeffProductRuleData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      DintOfCont gid.time gid.DCont n k
        =
      gid.Δt * gid.Davg n k := by
  intro n k
  rw [gid.hDavg_eq n k]
  unfold DintOfCont
  have hΔt0 : gid.Δt ≠ 0 := ne_of_gt gid.hΔt
  field_simp [hΔt0]

#check @hPint_eq_of_Pavg
#check @hDint_eq_of_Davg

-- ============================================================
-- SECTION 3: BRIDGE TO NSGalerkinIntervalIntegralActual
-- ============================================================

/-- The final product-rule data induce the previous
`GalerkinIntervalIntegralActualData`. -/
noncomputable def toGalerkinIntervalIntegralActualData
    {K_max : ℕ}
    (gid : GalerkinCoeffProductRuleData K_max) :
    GalerkinIntervalIntegralActualData K_max where
  Δt := gid.Δt
  hΔt := gid.hΔt
  XiCont := gid.XiCont
  PCont := gid.PCont
  DCont := gid.DCont
  time := gid.time
  htime_zero := gid.htime_zero
  htime_succ := gid.htime_succ
  hPCont_intervalIntegrable := gid.hPCont_intervalIntegrable
  hDCont_intervalIntegrable := gid.hDCont_intervalIntegrable
  hDavg_nonneg := by
    intro n k
    simpa [DavgOfCont, gid.hDavg_eq n k] using gid.hDavg_nonneg n k
  hXi_interval_eq := hXi_interval_eq_of_productRule gid

#check @toGalerkinIntervalIntegralActualData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the final product-rule identity already yields the conditional
discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_productRule_cutoff
    {K_max : ℕ}
    (gid : GalerkinCoeffProductRuleData K_max)
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
                    (toGalerkinIntervalIntegralActualData gid)))) n).P k
              ≤
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData gid)))) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData gid)))) n).P k
              ≤
            M * (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData gid)))) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData gid)))) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C *
            shellTotalEnstrophy
              (XiDiscrete
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData
                    (toGalerkinIntervalIntegralActualData gid)))) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy
          (XiDiscrete
            (toGalerkinCoeffODEContData
              (toGalerkinCoeffIntegratedProofData
                (toGalerkinIntervalIntegralActualData gid)))) (N0 + m)
          ≤
        (1 + M * C) ^ m *
          shellTotalEnstrophy
            (XiDiscrete
              (toGalerkinCoeffODEContData
                (toGalerkinCoeffIntegratedProofData
                  (toGalerkinIntervalIntegralActualData gid)))) N0 := by
  exact
    eventual_discrete_gronwall_of_intervalIntegral_cutoff
      (toGalerkinIntervalIntegralActualData gid)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_productRule_cutoff

end NSGalerkinCoeffProductRuleActual
