import NSBarrier.NSGalerkinCoeffIntegratedProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory

namespace NSGalerkinIntervalIntegralActual

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

/-
  Goal:
  define the actual integrated shellwise production / dissipation
  by interval integrals, then define the step averages, and derive
  the primitive data required by `NSGalerkinCoeffIntegratedProof`.
-/

-- ============================================================
-- SECTION 1: ACTUAL INTERVAL-INTEGRAL DEFINITIONS
-- ============================================================

/-- Integrated shellwise production over one time slab. -/
noncomputable def PintOfCont
    {K_max : ℕ}
    (time : ℕ → ℝ)
    (PCont : ℝ → Fin K_max → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∫ t in time n..time (n + 1), PCont t k

/-- Integrated shellwise dissipation over one time slab. -/
noncomputable def DintOfCont
    {K_max : ℕ}
    (time : ℕ → ℝ)
    (DCont : ℝ → Fin K_max → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∫ t in time n..time (n + 1), DCont t k

/-- Step-averaged shellwise production. -/
noncomputable def PavgOfCont
    {K_max : ℕ}
    (Δt : ℝ)
    (time : ℕ → ℝ)
    (PCont : ℝ → Fin K_max → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  PintOfCont time PCont n k / Δt

/-- Step-averaged shellwise dissipation. -/
noncomputable def DavgOfCont
    {K_max : ℕ}
    (Δt : ℝ)
    (time : ℕ → ℝ)
    (DCont : ℝ → Fin K_max → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  DintOfCont time DCont n k / Δt

#check @PintOfCont
#check @DintOfCont
#check @PavgOfCont
#check @DavgOfCont

-- ============================================================
-- SECTION 2: ACTUAL CONTINUOUS-TIME GALERKIN DATA
-- ============================================================

/-- Actual continuous-time Galerkin shell data.

The only genuinely analytic input here is the exact interval identity
coming from the Galerkin coefficient ODE:

  Xi(t_{n+1},k) - Xi(t_n,k)
    = ∫_{t_n}^{t_{n+1}} (P_k(t) - D_k(t)) dt

Everything else is algebraic packaging. -/
structure GalerkinIntervalIntegralActualData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 < Δt

  XiCont : ℝ → Fin K_max → ℝ
  PCont : ℝ → Fin K_max → ℝ
  DCont : ℝ → Fin K_max → ℝ

  /-- Discrete time grid, typically `time n = n * Δt`. -/
  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  /-- Interval integrability of shellwise production. -/
  hPCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable (fun t => PCont t k) volume (time n) (time (n + 1))

  /-- Interval integrability of shellwise dissipation. -/
  hDCont_intervalIntegrable :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable (fun t => DCont t k) volume (time n) (time (n + 1))

  /-- Nonnegativity of the step-averaged dissipation. -/
  hDavg_nonneg :
    ∀ n : ℕ, ∀ k : Fin K_max,
      0 ≤ DavgOfCont Δt time DCont n k

  /-- Exact integrated shellwise Galerkin identity. -/
  hXi_interval_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      XiCont (time (n + 1)) k - XiCont (time n) k
        =
      ∫ t in time n..time (n + 1), (PCont t k - DCont t k)

#check @GalerkinIntervalIntegralActualData

-- ============================================================
-- SECTION 3: SPLITTING THE INTERVAL IDENTITY
-- ============================================================

/-- The exact integrated shellwise identity splits into `Pint - Dint`. -/
theorem hXi_interval_eq_split
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      gid.XiCont (gid.time (n + 1)) k - gid.XiCont (gid.time n) k
        =
      PintOfCont gid.time gid.PCont n k - DintOfCont gid.time gid.DCont n k := by
  intro n k
  unfold PintOfCont DintOfCont
  rw [gid.hXi_interval_eq n k]
  simpa using
    intervalIntegral.integral_sub
      (gid.hPCont_intervalIntegrable n k)
      (gid.hDCont_intervalIntegrable n k)

#check @hXi_interval_eq_split

/-- Integrated production equals `Δt` times the step average. -/
theorem hPint_eq_dt_mul_Pavg
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      PintOfCont gid.time gid.PCont n k
        =
      gid.Δt * PavgOfCont gid.Δt gid.time gid.PCont n k := by
  intro n k
  unfold PavgOfCont
  have hΔt0 : gid.Δt ≠ 0 := ne_of_gt gid.hΔt
  field_simp [PintOfCont, hΔt0]

/-- Integrated dissipation equals `Δt` times the step average. -/
theorem hDint_eq_dt_mul_Davg
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      DintOfCont gid.time gid.DCont n k
        =
      gid.Δt * DavgOfCont gid.Δt gid.time gid.DCont n k := by
  intro n k
  unfold DavgOfCont
  have hΔt0 : gid.Δt ≠ 0 := ne_of_gt gid.hΔt
  field_simp [DintOfCont, hΔt0]

#check @hPint_eq_dt_mul_Pavg
#check @hDint_eq_dt_mul_Davg

-- ============================================================
-- SECTION 4: BRIDGE TO NSGalerkinCoeffIntegratedProof
-- ============================================================

/-- The actual interval-integral data induce the primitive
`GalerkinCoeffIntegratedProofData`. -/
noncomputable def toGalerkinCoeffIntegratedProofData
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max) :
    GalerkinCoeffIntegratedProofData K_max where
  Δt := gid.Δt
  hΔt := le_of_lt gid.hΔt
  XiCont := gid.XiCont
  Pint := PintOfCont gid.time gid.PCont
  Dint := DintOfCont gid.time gid.DCont
  Pavg := PavgOfCont gid.Δt gid.time gid.PCont
  Davg := DavgOfCont gid.Δt gid.time gid.DCont
  hDavg_nonneg := gid.hDavg_nonneg
  time := gid.time
  htime_zero := gid.htime_zero
  htime_succ := gid.htime_succ
  hXi_interval_eq := hXi_interval_eq_split gid
  hPint_eq := hPint_eq_dt_mul_Pavg gid
  hDint_eq := hDint_eq_dt_mul_Davg gid

#check @toGalerkinCoeffIntegratedProofData

-- ============================================================
-- SECTION 5: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the actual interval-integral Galerkin data already yield the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_intervalIntegral_cutoff
    {K_max : ℕ}
    (gid : GalerkinIntervalIntegralActualData K_max)
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
                  (toGalerkinCoeffIntegratedProofData gid))) n).P k
              ≤
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData gid))) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData gid))) n).P k
              ≤
            M * (instBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData gid))) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory
              (toGalerkinODEStepData
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData gid))) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy
                (XiDiscrete
                  (toGalerkinCoeffODEContData
                    (toGalerkinCoeffIntegratedProofData gid))) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy
          (XiDiscrete
            (toGalerkinCoeffODEContData
              (toGalerkinCoeffIntegratedProofData gid))) (N0 + m)
          ≤
        (1 + M * C) ^ m
          * shellTotalEnstrophy
              (XiDiscrete
                (toGalerkinCoeffODEContData
                  (toGalerkinCoeffIntegratedProofData gid))) N0 := by
  exact
    eventual_discrete_gronwall_of_integrated_proof_cutoff
      (toGalerkinCoeffIntegratedProofData gid)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_intervalIntegral_cutoff

end NSGalerkinIntervalIntegralActual
