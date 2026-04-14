import NSBarrier.NSGalerkinShellStepIdentity
import Mathlib.Tactic

namespace NSGalerkinODEActual

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open NSGalerkinShellStepIdentity

/-
  This file packages the last primitive Galerkin-Ode-side input:

    Xi_{n+1,k} - Xi_{n,k} = Δt * (P_inst(n,k) - D_inst(n,k))

  i.e. the exact shellwise one-step identity obtained by integrating the
  Galerkin ODE over a single time slab of length Δt.

  From this, we automatically build:
  - the integrated shell budget,
  - the shellwise exact step identity,
  - the total integrated hinc,
  - and the downstream conditional discrete Grönwall consequences.
-/

-- ============================================================
-- SECTION 1: PRIMITIVE GALERKIN ODE STEP DATA
-- ============================================================

/-- Primitive Galerkin ODE step data.

`Pinst` and `Dinst` are the instantaneous shellwise production/dissipation
on the `n`-th time slab, and `Xi` is the shellwise enstrophy quantity.

The key input is the exact one-step shellwise identity
obtained by integrating the Galerkin ODE over one time slab:
  Xi(n+1,k) - Xi(n,k) = Δt * (Pinst(n,k) - Dinst(n,k)).
-/
structure GalerkinODEStepData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 ≤ Δt

  Pinst : ℕ → Fin K_max → ℝ
  Dinst : ℕ → Fin K_max → ℝ
  Xi : ℕ → Fin K_max → ℝ

  hDinst_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Dinst n k

  /-- Exact shellwise ODE step identity after integrating over one time slab. -/
  hXi_step_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Xi (n + 1) k - Xi n k
        =
      Δt * (Pinst n k - Dinst n k)

#check @GalerkinODEStepData

-- ============================================================
-- SECTION 2: INSTANTANEOUS / INTEGRATED BUDGET TRAJECTORIES
-- ============================================================

/-- The instantaneous shell-budget trajectory associated to the Galerkin ODE data. -/
noncomputable def instBudgetTrajectory
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) : BudgetTrajectory K_max :=
  fun n =>
    { P := ode.Pinst n
      D := ode.Dinst n
      D_nonneg := ode.hDinst_nonneg n }

#check @instBudgetTrajectory

/-- The integrated shell-budget trajectory obtained by scaling the instantaneous
budget by the time-step `Δt`. -/
noncomputable def intBudgetTrajectory
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) : BudgetTrajectory K_max :=
  scaleBudgetTrajectory ode.Δt ode.hΔt (instBudgetTrajectory ode)

#check @intBudgetTrajectory

/-- The primitive Galerkin ODE data induce the previously defined
`GalerkinIntegratedBudgetData`. -/
noncomputable def toGalerkinIntegratedBudgetData
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) : GalerkinIntegratedBudgetData K_max where
  Δt := ode.Δt
  hΔt := ode.hΔt
  instTraj := instBudgetTrajectory ode
  intTraj := intBudgetTrajectory ode
  hP_int := by
    intro n k
    simp [intBudgetTrajectory, instBudgetTrajectory, scaleBudgetTrajectory, scaleShellBudget]
  hD_int := by
    intro n k
    simp [intBudgetTrajectory, instBudgetTrajectory, scaleBudgetTrajectory, scaleShellBudget]

#check @toGalerkinIntegratedBudgetData

-- ============================================================
-- SECTION 3: SHELLWISE EXACT STEP IDENTITY
-- ============================================================

/-- The primitive Galerkin ODE step identity is exactly the shellwise identity
for the integrated shell budget. -/
theorem hstep_shell_eq_of_galerkinODE
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      ode.Xi (n + 1) k - ode.Xi n k
        =
      (intBudgetTrajectory ode n).P k - (intBudgetTrajectory ode n).D k := by
  intro n k
  calc
    ode.Xi (n + 1) k - ode.Xi n k
      =
    ode.Δt * (ode.Pinst n k - ode.Dinst n k) := ode.hXi_step_eq n k
    _ =
    (ode.Δt * ode.Pinst n k) - (ode.Δt * ode.Dinst n k) := by ring
    _ =
    (intBudgetTrajectory ode n).P k - (intBudgetTrajectory ode n).D k := by
      simp [intBudgetTrajectory, instBudgetTrajectory, scaleBudgetTrajectory, scaleShellBudget]

#check @hstep_shell_eq_of_galerkinODE

/-- The primitive Galerkin ODE data induce the previous
`GalerkinShellStepIdentityData`. -/
noncomputable def toGalerkinShellStepIdentityData
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) : GalerkinShellStepIdentityData K_max where
  budgetData := toGalerkinIntegratedBudgetData ode
  Xi := ode.Xi
  hstep_shell_eq := by
    intro n k
    simpa [toGalerkinIntegratedBudgetData, intBudgetTrajectory]
      using hstep_shell_eq_of_galerkinODE ode n k

#check @toGalerkinShellStepIdentityData

-- ============================================================
-- SECTION 4: TOTAL ENSTROPHY IDENTITY AND HINC
-- ============================================================

/-- Total enstrophy identity obtained from the primitive Galerkin ODE data. -/
theorem step_total_eq_of_galerkinODE
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy ode.Xi (n + 1) - shellTotalEnstrophy ode.Xi n
        =
      shellNetSource (intBudgetTrajectory ode n) Finset.univ := by
  intro n
  simpa [toGalerkinShellStepIdentityData, intBudgetTrajectory]
    using NSGalerkinShellStepIdentity.step_total_eq
      (toGalerkinShellStepIdentityData ode) n

/-- Integrated one-step shell-budget inequality obtained from the primitive
Galerkin ODE data. -/
theorem hinc_gal_of_galerkinODE
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max) :
    ∀ n : ℕ,
      shellTotalEnstrophy ode.Xi (n + 1) - shellTotalEnstrophy ode.Xi n
        ≤
      shellNetSource (intBudgetTrajectory ode n) Finset.univ := by
  intro n
  exact le_of_eq (step_total_eq_of_galerkinODE ode n)

#check @step_total_eq_of_galerkinODE
#check @hinc_gal_of_galerkinODE

-- ============================================================
-- SECTION 5: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the primitive Galerkin ODE step identity already yields the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_galerkinODE_cutoff
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory ode n).P k ≤ (instBudgetTrajectory ode n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory ode n).P k ≤ M * (instBudgetTrajectory ode n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (intBudgetTrajectory ode n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy ode.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy ode.Xi (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy ode.Xi N0 := by
  exact
    eventual_discrete_gronwall_of_shellwise_step_identity_cutoff
      (toGalerkinShellStepIdentityData ode)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

/-- Barrier-specialized version. -/
theorem eventual_discrete_gronwall_of_galerkinODE_barrier_fixed_cutoff
    {K_max : ℕ}
    (ode : GalerkinODEStepData K_max)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max,
            (instBudgetTrajectory ode n).D k < (instBudgetTrajectory ode n).P k →
            Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory ode n).P k ≤ (instBudgetTrajectory ode n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory ode n).P k ≤ M * (instBudgetTrajectory ode n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (intBudgetTrajectory ode n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy ode.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy ode.Xi (N0 + m)
          ≤
        (1 + M * C) ^ m * shellTotalEnstrophy ode.Xi N0 := by
  exact
    eventual_discrete_gronwall_of_shellwise_step_identity_barrier_fixed_cutoff
      (toGalerkinShellStepIdentityData ode)
      Φ ν M C Ncut
      hν hM hMC
      hbar htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_galerkinODE_cutoff
#check @eventual_discrete_gronwall_of_galerkinODE_barrier_fixed_cutoff

end NSGalerkinODEActual
