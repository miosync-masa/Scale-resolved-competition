import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3ShellActual

/-- Physical space for the Euclidean branch: `\mathbb{R}^3`. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Frequency space for the Euclidean branch: also `\mathbb{R}^3`. -/
abbrev Frequency := EuclideanSpace ℝ (Fin 3)

/-- Lebesgue measure on `\mathbb{R}^3`. -/
noncomputable abbrev μR3 : Measure R3 :=
  (MeasureTheory.volume : Measure R3)

/-- Complex scalar `L²(\mathbb{R}^3)`. -/
noncomputable abbrev L2R3 :=
  MeasureTheory.Lp ℂ (2 : ℝ≥0∞) μR3

/-- Closed low-frequency ball of radius `R`. -/
def lowBall (R : ℝ) : Set Frequency :=
  {ξ | ‖ξ‖ ≤ R}

/-- Euclidean annulus `R1 ≤ |ξ| < R2`. -/
def annulus (R1 R2 : ℝ) : Set Frequency :=
  {ξ | R1 ≤ ‖ξ‖ ∧ ‖ξ‖ < R2}

/-- Dyadic shell `2^j ≤ |ξ| < 2^(j+1)`. -/
def dyadicAnnulus (j : ℕ) : Set Frequency :=
  annulus ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))

/-- Membership in the low-frequency ball unfolds to the norm inequality. -/
theorem mem_lowBall_iff
    {R : ℝ} {ξ : Frequency} :
    ξ ∈ lowBall R ↔ ‖ξ‖ ≤ R := by
  rfl

/-- Membership in an annulus unfolds to the pair of radial inequalities. -/
theorem mem_annulus_iff
    {R1 R2 : ℝ} {ξ : Frequency} :
    ξ ∈ annulus R1 R2 ↔ R1 ≤ ‖ξ‖ ∧ ‖ξ‖ < R2 := by
  rfl

/-- Membership in a dyadic annulus unfolds to the corresponding dyadic radial bounds. -/
theorem mem_dyadicAnnulus_iff
    {j : ℕ} {ξ : Frequency} :
    ξ ∈ dyadicAnnulus j
      ↔
    (2 : ℝ) ^ j ≤ ‖ξ‖ ∧ ‖ξ‖ < (2 : ℝ) ^ (j + 1) := by
  rfl

/-- Every dyadic annulus sits inside the next larger low-frequency ball. -/
theorem dyadicAnnulus_subset_lowBall_succ
    (j : ℕ) :
    dyadicAnnulus j ⊆ lowBall ((2 : ℝ) ^ (j + 1)) := by
  intro ξ hξ
  rcases hξ with ⟨_, hupper⟩
  exact le_of_lt hupper

/-- Thin package recording the Euclidean-domain backend used by the `R³` branch. -/
structure R3FrequencyBackend where
  domain : Type
  frequency : Type
  stateSpace : Type
  measure : Measure R3

/-- The concrete `R³` backend used by the Euclidean counterexample branch. -/
noncomputable def actualR3FrequencyBackend : R3FrequencyBackend where
  domain := R3
  frequency := Frequency
  stateSpace := L2R3
  measure := μR3

/-- C1 backend theorem: the Euclidean branch is based on `R³` in physical space,
continuous frequency space `R³`, Lebesgue measure, and scalar `L²(R³)`. -/
theorem R3_domain_and_frequency_backend :
    actualR3FrequencyBackend.domain = R3 ∧
    actualR3FrequencyBackend.frequency = Frequency ∧
    actualR3FrequencyBackend.stateSpace = L2R3 ∧
    actualR3FrequencyBackend.measure = μR3 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end NSR3ShellActual
