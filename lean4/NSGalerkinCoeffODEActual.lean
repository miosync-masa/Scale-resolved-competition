import NSBarrier.NSGalerkinODEActual
import Mathlib.Tactic

namespace NSGalerkinCoeffODEActual

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open NSGalerkinShellStepIdentity
open NSGalerkinODEActual

/-!
  Goal:
  derive the primitive Galerkin ODE step data from continuous-time
  shellwise coefficient dynamics, in integrated form.
-/

-- ============================================================
-- SECTION 1: CONTINUOUS-TIME SHELLWISE ODE / INTEGRATED DATA
-- ============================================================

/-- Continuous-time Galerkin shell data on a fixed uniform time grid.

`XiCont t k`, `PCont t k`, `DCont t k` are the shellwise enstrophy / production /
dissipation at continuous time `t`.

We sample them on the discrete grid `t_n = t0 + n * Δt`.

The core actual analytic input is the integrated shellwise identity:
  Xi(t_{n+1},k) - Xi(t_n,k) = ∫_{t_n}^{t_{n+1}} (P_k - D_k).

To connect with the already-built discrete chain, we also package
step-averaged shell production / dissipation:
  Pavg(n,k) = (1/Δt) ∫_{t_n}^{t_{n+1}} P_k
  Davg(n,k) = (1/Δt) ∫_{t_n}^{t_{n+1}} D_k.
-/
structure GalerkinCoeffODEContData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 ≤ Δt

  XiCont : ℝ → Fin K_max → ℝ
  PCont : ℝ → Fin K_max → ℝ
  DCont : ℝ → Fin K_max → ℝ

  /-- Step-averaged production and dissipation. -/
  Pavg : ℕ → Fin K_max → ℝ
  Davg : ℕ → Fin K_max → ℝ
  hDavg_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Davg n k

  /-- Discrete time grid. -/
  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  /-- Exact integrated shellwise coefficient identity. -/
  hXi_integrated :
    ∀ n : ℕ, ∀ k : Fin K_max,
      XiCont (time (n + 1)) k - XiCont (time n) k
        =
      Δt * (Pavg n k - Davg n k)

#check @GalerkinCoeffODEContData

-- ============================================================
-- SECTION 2: DISCRETE SHELLWISE DATA EXTRACTED FROM CONTINUOUS TIME
-- ============================================================

/-- Sampled shellwise enstrophy on the discrete time grid. -/
noncomputable def XiDiscrete
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max) : ℕ → Fin K_max → ℝ :=
  fun n k => ode.XiCont (ode.time n) k

#check @XiDiscrete

/-- The continuous-time coefficient ODE data induce the primitive
discrete Galerkin ODE step data. -/
noncomputable def toGalerkinODEStepData
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max) : GalerkinODEStepData K_max where
  Δt := ode.Δt
  hΔt := ode.hΔt
  Pinst := ode.Pavg
  Dinst := ode.Davg
  Xi := XiDiscrete ode
  hDinst_nonneg := ode.hDavg_nonneg
  hXi_step_eq := by
    intro n k
    simpa [XiDiscrete] using ode.hXi_integrated n k

#check @toGalerkinODEStepData

-- ============================================================
-- SECTION 3: DIRECT SHELLWISE / TOTAL CONSEQUENCES
-- ============================================================

/-- Shellwise exact step identity on the sampled time grid. -/
theorem hstep_shell_eq_of_continuous_coeffODE
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      XiDiscrete ode (n + 1) k - XiDiscrete ode n k
        =
      (intBudgetTrajectory (toGalerkinODEStepData ode) n).P k
        -
      (intBudgetTrajectory (toGalerkinODEStepData ode) n).D k := by
  intro n k
  simpa [toGalerkinODEStepData, XiDiscrete]
    using hstep_shell_eq_of_galerkinODE (toGalerkinODEStepData ode) n k

/-- Total integrated enstrophy identity on the sampled time grid. -/
theorem step_total_eq_of_continuous_coeffODE
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy (XiDiscrete ode) (n + 1)
        -
      shellTotalEnstrophy (XiDiscrete ode) n
        =
      shellNetSource (intBudgetTrajectory (toGalerkinODEStepData ode) n) Finset.univ := by
  intro n
  simpa [toGalerkinODEStepData, XiDiscrete]
    using step_total_eq_of_galerkinODE (toGalerkinODEStepData ode) n

/-- One-step integrated shell-budget inequality on the sampled time grid. -/
theorem hinc_gal_of_continuous_coeffODE
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy (XiDiscrete ode) (n + 1)
        -
      shellTotalEnstrophy (XiDiscrete ode) n
        ≤
      shellNetSource (intBudgetTrajectory (toGalerkinODEStepData ode) n) Finset.univ := by
  intro n
  exact le_of_eq (step_total_eq_of_continuous_coeffODE ode n)

#check @hstep_shell_eq_of_continuous_coeffODE
#check @step_total_eq_of_continuous_coeffODE
#check @hinc_gal_of_continuous_coeffODE

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the continuous-time Galerkin coefficient ODE data already yield the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_continuous_coeffODE_cutoff
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).P k
              ≤
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).P k
              ≤
            M * (instBudgetTrajectory (toGalerkinODEStepData ode) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory (toGalerkinODEStepData ode) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy (XiDiscrete ode) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy (XiDiscrete ode) (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy (XiDiscrete ode) N0 := by
  exact
    eventual_discrete_gronwall_of_galerkinODE_cutoff
      (toGalerkinODEStepData ode)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

/-- Barrier-specialized version. -/
theorem eventual_discrete_gronwall_of_continuous_coeffODE_barrier_fixed_cutoff
    {K_max : ℕ}
    (ode : GalerkinCoeffODEContData K_max)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max,
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).D k
              <
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).P k →
            Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).P k
              ≤
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory (toGalerkinODEStepData ode) n).P k
              ≤
            M * (instBudgetTrajectory (toGalerkinODEStepData ode) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory (toGalerkinODEStepData ode) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy (XiDiscrete ode) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy (XiDiscrete ode) (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy (XiDiscrete ode) N0 := by
  exact
    eventual_discrete_gronwall_of_galerkinODE_barrier_fixed_cutoff
      (toGalerkinODEStepData ode)
      Φ ν M C Ncut
      hν hM hMC
      hbar htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_continuous_coeffODE_cutoff
#check @eventual_discrete_gronwall_of_continuous_coeffODE_barrier_fixed_cutoff

end NSGalerkinCoeffODEActual
