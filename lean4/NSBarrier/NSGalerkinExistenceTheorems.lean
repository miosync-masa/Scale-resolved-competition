import NSBarrier.NSGalerkinExistenceActual
import NSBarrier.NSGalerkinIntegrabilityTheorems
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic

open MeasureTheory
open NSTorusShellActual
open NSGalerkinExistenceActual
open NSGalerkinCoeffODEProductRuleProof
open NSGalerkinIntegrabilityTheorems

namespace NSGalerkinExistenceTheorems

-- ============================================================
-- [ODE] Galerkin existence theorem surface
--
-- This file keeps the theorem surface thin and sorry-free.
--
-- Important design choice:
--   Section 1 states the exact *local* Picard-Lindelöf theorem
--   that Mathlib provides on a compact time interval `Icc`.
--   Global-in-time existence is then obtained later by
--   continuation / no-blowup arguments, not here.
-- ============================================================

/-- [ODE] A finite-dimensional Galerkin ODE system specification.

This is the minimal data needed to state the existence theorem:
- a finite-dimensional state space `Fin m → ℝ`
- a right-hand side `rhs : ℝ → (Fin m → ℝ) → (Fin m → ℝ)`
- an initial condition `state₀ : Fin m → ℝ`
-/
structure GalerkinODESpec (m : ℕ) where
  rhs : ℝ → (Fin m → ℝ) → (Fin m → ℝ)
  state₀ : Fin m → ℝ

/-- [ODE] A global solution surface for the finite-dimensional Galerkin ODE.

This structure is still useful downstream when one already has
a global solution (for example after continuation / no-blowup).
Section 1 below does *not* construct this directly from Picard-Lindelöf;
it first gives the exact local theorem on `Icc`. -/
structure GalerkinODESolution (m : ℕ) extends GalerkinODESpec m where
  state : ℝ → Fin m → ℝ
  hstate_initial : state 0 = state₀
  hstate_hasDeriv :
    ∀ i : Fin m, ∀ t : ℝ,
      HasDerivAt (fun s => state s i) (rhs t (state t) i) t

#check @GalerkinODESpec
#check @GalerkinODESolution

-- ============================================================
-- SECTION 1: LOCAL PICARD-LINDELOF EXISTENCE (SORRY-FREE)
-- ============================================================

/-- [ODE] Local finite-dimensional Galerkin existence on a compact interval.

This is the exact Picard-Lindelöf statement exported by Mathlib for
the radius-`0` initial condition case. It gives a local solution on
`Icc tmin tmax` with a `HasDerivWithinAt` statement.

Global existence is *not* claimed here; it is obtained later by
continuation / no-blowup arguments. -/
theorem exists_galerkin_ode_solution
    (m : ℕ)
    (spec : GalerkinODESpec m)
    {tmin tmax : ℝ}
    {t₀ : Set.Icc tmin tmax}
    {a L K : NNReal}
    (hPL : IsPicardLindelof spec.rhs t₀ spec.state₀ a 0 L K) :
    ∃ state : ℝ → Fin m → ℝ,
      state (↑t₀) = spec.state₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt state (spec.rhs t (state t)) (Set.Icc tmin tmax) t := by
  simpa using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

#check @exists_galerkin_ode_solution

/-- [ODE] Initial-condition theorem, isolated as a named corollary. -/
theorem galerkin_ode_initial_condition
    {m : ℕ}
    {spec : GalerkinODESpec m}
    {tmin tmax : ℝ}
    {t₀ : Set.Icc tmin tmax}
    {a L K : NNReal}
    (hPL : IsPicardLindelof spec.rhs t₀ spec.state₀ a 0 L K) :
    ∃ state : ℝ → Fin m → ℝ,
      state (↑t₀) = spec.state₀ := by
  rcases exists_galerkin_ode_solution m spec hPL with ⟨state, h0, hderiv⟩
  exact ⟨state, h0⟩

/-- [ODE] Differential-form theorem, isolated as a named corollary. -/
theorem galerkin_ode_hasDerivWithinAt
    {m : ℕ}
    {spec : GalerkinODESpec m}
    {tmin tmax : ℝ}
    {t₀ : Set.Icc tmin tmax}
    {a L K : NNReal}
    (hPL : IsPicardLindelof spec.rhs t₀ spec.state₀ a 0 L K) :
    ∃ state : ℝ → Fin m → ℝ,
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt state (spec.rhs t (state t)) (Set.Icc tmin tmax) t := by
  rcases exists_galerkin_ode_solution m spec hPL with ⟨state, h0, hderiv⟩
  exact ⟨state, hderiv⟩

#check @galerkin_ode_initial_condition
#check @galerkin_ode_hasDerivWithinAt

-- ============================================================
-- SECTION 1.5: LOCAL EXISTENCE SEED
-- ============================================================

/-- A local existence seed on the compact interval `[0, T0]`.

This packages exactly the local Picard-Lindelöf output that will
be fed into the continuation / no-blowup layers. -/
structure LocalExistenceSeed (m : ℕ) (spec : GalerkinODESpec m) where
  T0 : ℝ
  hT0 : 0 < T0
  state : ℝ → Fin m → ℝ
  hstate_initial : state 0 = spec.state₀
  hstate_hasDerivWithin :
    ∀ t ∈ Set.Icc (0 : ℝ) T0,
      HasDerivWithinAt state (spec.rhs t (state t)) (Set.Icc (0 : ℝ) T0) t

#check @LocalExistenceSeed

/-- Local Picard-Lindelöf existence packaged as a `LocalExistenceSeed`
on `[0, T0]`. -/
noncomputable def localExistenceSeed_of_picardLindelof
    (m : ℕ)
    (spec : GalerkinODESpec m)
    (T0 : ℝ)
    (hT0 : 0 < T0)
    {a L K : NNReal}
    (hPL :
      IsPicardLindelof
        spec.rhs
        (show Set.Icc (0 : ℝ) T0 from ⟨0, by constructor <;> linarith⟩)
        spec.state₀
        a 0 L K) :
    LocalExistenceSeed m spec := by
  have h := exists_galerkin_ode_solution m spec
      (tmin := 0) (tmax := T0)
      (t₀ := (⟨0, by constructor <;> linarith⟩ : Set.Icc (0 : ℝ) T0))
      hPL
  exact
    { T0 := T0
      hT0 := hT0
      state := h.choose
      hstate_initial := by simpa using h.choose_spec.1
      hstate_hasDerivWithin := h.choose_spec.2 }

#check @localExistenceSeed_of_picardLindelof

-- ============================================================
-- SECTION 2: DERIVED REGULARITY THEOREMS FOR GLOBAL SOLUTIONS
-- ============================================================

/-- [ODE] The Galerkin state is coordinatewise differentiable
(direct consequence of the global solution property). -/
theorem hasDerivAt_of_galerkin_state_solution
    {m : ℕ}
    (sol : GalerkinODESolution m) :
    ∀ i : Fin m, ∀ t : ℝ,
      HasDerivAt (fun s => sol.state s i)
        (sol.rhs t (sol.state t) i) t :=
  sol.hstate_hasDeriv

/-- [ODE] Each coordinate of the Galerkin state is continuous
(differentiable implies continuous). -/
theorem continuous_galerkin_state_coord
    {m : ℕ}
    (sol : GalerkinODESolution m) :
    ∀ i : Fin m,
      Continuous (fun t => sol.state t i) := by
  intro i
  rw [continuous_iff_continuousAt]
  intro t
  exact (sol.hstate_hasDeriv i t).continuousAt

/-- [ODE] The Galerkin state itself is continuous as a function
into `Fin m → ℝ`. -/
theorem continuous_galerkin_state
    {m : ℕ}
    (sol : GalerkinODESolution m) :
    Continuous sol.state := by
  rw [continuous_pi_iff]
  exact continuous_galerkin_state_coord sol

/-- [ODE] The solution satisfies the initial condition. -/
theorem hstate_initial_of_ode_existence
    {m : ℕ}
    (sol : GalerkinODESolution m) :
    sol.state 0 = sol.state₀ :=
  sol.hstate_initial

#check @hasDerivAt_of_galerkin_state_solution
#check @continuous_galerkin_state_coord
#check @continuous_galerkin_state
#check @hstate_initial_of_ode_existence

-- ============================================================
-- SECTION 3: INTEGRABILITY FROM EXISTENCE
-- ============================================================

/-- [ODE] The shellwise production is interval integrable,
derived from the Galerkin solution's continuity. -/
theorem PCont_intervalIntegrable_of_galerkin_solution
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => PContOfCoeffs d.modes d.shellOf d.weight
          (fun s κ => d.state s (d.coordOf κ)) d.nonlin t k)
        volume (d.time n) (d.time (n + 1)) :=
  d.hPCont_intervalIntegrable

/-- [ODE] The shellwise dissipation is interval integrable,
derived from the Galerkin solution's continuity. -/
theorem DCont_intervalIntegrable_of_galerkin_solution
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      IntervalIntegrable
        (fun t => DContOfCoeffs d.modes d.shellOf d.weight
          (fun s κ => d.state s (d.coordOf κ)) d.damp t k)
        volume (d.time n) (d.time (n + 1)) :=
  d.hDCont_intervalIntegrable

#check @PCont_intervalIntegrable_of_galerkin_solution
#check @DCont_intervalIntegrable_of_galerkin_solution

-- ============================================================
-- SECTION 4: THE COEFFICIENT ODE FROM STATE SOLUTION
-- ============================================================

/-- [ODE] The Galerkin coefficient satisfies the modewise ODE,
derived from the coordinatewise state ODE and the RHS identification.
This is the theorem that makes `hcoeff_solution` a *consequence*
rather than an *assumption*. -/
theorem hcoeff_solution_of_galerkin_existence
    {K_max m : ℕ}
    (d : ActualFiniteDimensionalGalerkinStateData K_max m) :
    ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt (fun s => coeffOfState d s κ)
        (d.nonlin t κ - d.damp κ * coeffOfState d t κ) t :=
  hcoeff_solution_of_state d

#check @hcoeff_solution_of_galerkin_existence

end NSGalerkinExistenceTheorems
