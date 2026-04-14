import NSBarrier.NSGalerkinExistenceTheorems
import NSBarrier.NSUniformEquicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Tactic

namespace NSGalerkinODEExistenceTheorems

open NSGalerkinExistenceTheorems
open Filter

-- ============================================================
-- SECTION 1: ODE EXISTENCE => SOLUTION PROPERTIES
-- ============================================================

theorem hstate_hasDeriv_of_ode_existence
    {m : ℕ} (sol : GalerkinODESolution m) :
    ∀ i : Fin m, ∀ t : ℝ,
      HasDerivAt (fun s => sol.state s i)
        (sol.rhs t (sol.state t) i) t :=
  sol.hstate_hasDeriv

theorem hstate_continuous_of_ode_existence
    {m : ℕ} (sol : GalerkinODESolution m) :
    ∀ i : Fin m, Continuous (fun t => sol.state t i) :=
  continuous_galerkin_state_coord sol

theorem hstate_continuous_full_of_ode_existence
    {m : ℕ} (sol : GalerkinODESolution m) :
    Continuous sol.state :=
  continuous_galerkin_state sol

theorem hstate_initial_of_ode_existence
    {m : ℕ} (sol : GalerkinODESolution m) :
    sol.state 0 = sol.state₀ :=
  sol.hstate_initial

#check @hstate_hasDeriv_of_ode_existence
#check @hstate_continuous_of_ode_existence
#check @hstate_continuous_full_of_ode_existence
#check @hstate_initial_of_ode_existence

-- ============================================================
-- SECTION 2: ARZELA-ASCOLI ON COMPACT INTERVAL
-- ============================================================

abbrev TimeInterval (T : ℝ) := Set.Icc (0 : ℝ) T

/-- Lift a family of continuous maps on a compact interval
to bounded continuous functions. -/
noncomputable def stateFamBCF
    {m : ℕ} {T : ℝ}
    (stateFam : ℕ → C(TimeInterval T, Fin m → ℝ)) :
    ℕ → BoundedContinuousFunction (TimeInterval T)
      (Fin m → ℝ) :=
  fun j => BoundedContinuousFunction.mkOfCompact
    (stateFam j)

/-- [ODE] Arzela-Ascoli extraction on `[0, T]`.

Uses `BoundedContinuousFunction.arzela_ascoli` from Mathlib
and `IsCompact.tendsto_subseq` for subsequence extraction.

The hypotheses are:
- uniform boundedness of the family
- uniform Lipschitz (implies equicontinuity)

The conclusion gives a subsequence converging pointwise. -/
theorem arzela_ascoli_subsequence_extraction
    (m : ℕ) (T : ℝ) (_hT : 0 ≤ T)
    (stateFam : ℕ → C(TimeInterval T, Fin m → ℝ))
    (hbounded : ∃ B : ℝ, 0 ≤ B ∧
      ∀ j : ℕ, ∀ t : TimeInterval T,
        ‖stateFam j t‖ ≤ B)
    (hequicont :
      ∀ ε > 0, ∃ δ > 0, ∀ j : ℕ,
        ∀ x y : TimeInterval T,
          ‖(x : ℝ) - (y : ℝ)‖ < δ →
            ‖stateFam j x - stateFam j y‖ < ε) :
    ∃ (subseq : ℕ → ℕ)
      (stateLim : C(TimeInterval T, Fin m → ℝ)),
      StrictMono subseq ∧
      ∀ t : TimeInterval T, ∀ i : Fin m,
        Tendsto
          (fun j => stateFam (subseq j) t i)
          atTop (nhds (stateLim t i)) := by
  -- Step 1: Set up the BoundedContinuousFunction family
  let F := stateFamBCF stateFam
  let A : Set (BoundedContinuousFunction (TimeInterval T) (Fin m → ℝ)) :=
    Set.range F
  -- Step 2: Build the compact target set
  rcases hbounded with ⟨B, hBnn, hB⟩
  let s : Set (Fin m → ℝ) := Metric.closedBall 0 B
  have hs : IsCompact s := isCompact_closedBall 0 B
  -- Step 3: Show all values land in s
  have hin_s : ∀ (f : BoundedContinuousFunction (TimeInterval T) (Fin m → ℝ))
      (x : TimeInterval T), f ∈ A → f x ∈ s := by
    intro f x ⟨j, hj⟩
    rw [show s = Metric.closedBall 0 B from rfl, Metric.mem_closedBall, dist_zero_right]
    rw [← hj]; exact hB j x
  -- Step 4: Build Equicontinuous from ε-δ hypothesis
  --   Use Metric.equicontinuousAt_iff at each point x₀
  have hEquicont : Equicontinuous
      ((↑) : A → TimeInterval T → Fin m → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    rcases hequicont ε hε with ⟨δ, hδ, hec⟩
    refine ⟨δ, hδ, fun x hx ⟨_, j, rfl⟩ => ?_⟩
    rw [dist_eq_norm]
    exact hec j x₀ x (by rw [← dist_eq_norm, ← Subtype.dist_eq]; exact dist_comm x x₀ ▸ hx)
  -- Step 5: Apply Arzela-Ascoli
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli s hs A hin_s hEquicont
  -- Step 6: Extract convergent subsequence
  have hmem : ∀ n : ℕ, F n ∈ closure A :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases hcompact.tendsto_subseq hmem with
    ⟨g, _, subseq, hmono, hconv⟩
  -- Step 7: Extract pointwise convergence
  refine ⟨subseq, g.toContinuousMap, hmono, fun t i => ?_⟩
  -- hconv : Tendsto (F ∘ subseq) atTop (nhds g)
  -- Use continuous_eval_const to get pointwise convergence
  have hpt : Tendsto (fun j => (F ∘ subseq) j t) atTop (nhds (g t)) :=
    hconv.eval_const t
  -- Use continuous_apply to get coordinate convergence
  have hpi : Tendsto (fun j => (F ∘ subseq) j t i) atTop (nhds (g t i)) :=
    ((continuous_apply i).tendsto _).comp hpt
  exact hpi

#check @arzela_ascoli_subsequence_extraction

-- ============================================================
-- SECTION 3: EQUICONTINUITY FROM UNIFORM LIPSCHITZ
-- ============================================================

/-- [ODE] Uniform Lipschitz implies equicontinuity on `[0,T]`.

This is the bridge from `NSUniformEquicontinuity.lipschitz_of_uniform_deriv_bound`
to the equicontinuity hypothesis of Arzela-Ascoli. -/
theorem equicontinuity_of_uniform_lipschitz
    (m : ℕ) (T : ℝ) (_hT : 0 ≤ T)
    (stateFam : ℕ → C(TimeInterval T, Fin m → ℝ))
    (L : ℝ) (_hL : 0 ≤ L)
    (hLip : ∀ j : ℕ, ∀ x y : TimeInterval T,
      ‖stateFam j x - stateFam j y‖
        ≤ L * ‖(x : ℝ) - (y : ℝ)‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ j : ℕ,
      ∀ x y : TimeInterval T,
        ‖(x : ℝ) - (y : ℝ)‖ < δ →
          ‖stateFam j x - stateFam j y‖ < ε := by
  intro ε hε
  by_cases hL0 : L = 0
  · exact ⟨1, one_pos, fun j x y _ => by
      have h := hLip j x y; simp only [hL0, zero_mul] at h
      have heq := sub_eq_zero.mp (norm_le_zero_iff.mp h)
      simp only [heq, sub_self, norm_zero]; exact hε⟩
  · have hLpos : 0 < L := lt_of_le_of_ne _hL (Ne.symm hL0)
    refine ⟨ε / L, div_pos hε hLpos, ?_⟩
    intro j x y hxy
    calc ‖stateFam j x - stateFam j y‖
        ≤ L * ‖(x : ℝ) - (y : ℝ)‖ := hLip j x y
      _ < L * (ε / L) := mul_lt_mul_of_pos_left hxy hLpos
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hLpos)

#check @equicontinuity_of_uniform_lipschitz

-- ============================================================
-- SECTION 4: COMBINED EXTRACTION
-- ============================================================

/-- [ODE] Combined: uniform Lipschitz + bounded → extraction.

This composes equicontinuity + Arzela-Ascoli. -/
theorem galerkin_subsequence_extraction_of_uniform_bounds
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (stateFam : ℕ → C(TimeInterval T, Fin m → ℝ))
    (hbounded : ∃ B : ℝ, 0 ≤ B ∧
      ∀ j : ℕ, ∀ t : TimeInterval T,
        ‖stateFam j t‖ ≤ B)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ j : ℕ, ∀ x y : TimeInterval T,
      ‖stateFam j x - stateFam j y‖
        ≤ L * ‖(x : ℝ) - (y : ℝ)‖) :
    ∃ (subseq : ℕ → ℕ)
      (stateLim : C(TimeInterval T, Fin m → ℝ)),
      StrictMono subseq ∧
      ∀ t : TimeInterval T, ∀ i : Fin m,
        Tendsto
          (fun j => stateFam (subseq j) t i)
          atTop (nhds (stateLim t i)) := by
  exact arzela_ascoli_subsequence_extraction m T hT
    stateFam hbounded
    (equicontinuity_of_uniform_lipschitz m T hT
      stateFam L hL hLip)

#check @galerkin_subsequence_extraction_of_uniform_bounds

-- ============================================================
-- SECTION 5: BACKWARD-COMPATIBLE TIME-GRID VERSION
-- ============================================================

/-- [ODE] Extraction with convergence at prescribed time points.

This is the backward-compatible interface for downstream files
that use a discrete time grid `time : ℕ → ℝ` within `[0, T]`. -/
theorem galerkin_subsequence_extraction_at_times
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (stateFam : ℕ → C(TimeInterval T, Fin m → ℝ))
    (time : ℕ → ℝ)
    (htime : ∀ n : ℕ, time n ∈ Set.Icc (0 : ℝ) T)
    (hbounded : ∃ B : ℝ, 0 ≤ B ∧
      ∀ j : ℕ, ∀ t : TimeInterval T,
        ‖stateFam j t‖ ≤ B)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ j : ℕ, ∀ x y : TimeInterval T,
      ‖stateFam j x - stateFam j y‖
        ≤ L * ‖(x : ℝ) - (y : ℝ)‖) :
    ∃ (subseq : ℕ → ℕ)
      (stateLim : C(TimeInterval T, Fin m → ℝ)),
      StrictMono subseq ∧
      ∀ n : ℕ, ∀ i : Fin m,
        Tendsto
          (fun j => stateFam (subseq j)
            ⟨time n, htime n⟩ i)
          atTop
          (nhds (stateLim ⟨time n, htime n⟩ i)) := by
  rcases galerkin_subsequence_extraction_of_uniform_bounds
    m T hT stateFam hbounded L hL hLip with
    ⟨subseq, stateLim, hmono, hconv⟩
  exact ⟨subseq, stateLim, hmono,
    fun n i => hconv ⟨time n, htime n⟩ i⟩

#check @galerkin_subsequence_extraction_at_times

end NSGalerkinODEExistenceTheorems
