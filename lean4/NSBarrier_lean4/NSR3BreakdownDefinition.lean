import NSBarrier.NSR3SolutionPackage
import Mathlib.Tactic

namespace NSR3BreakdownDefinition

open NSR3SolutionPackage

/-- Euclidean actual solution package used by the breakdown branch. -/
abbrev R3ActualSolutionPackage (K_max : ℕ) :=
  NSR3SolutionPackage.R3ActualSolutionPackage K_max

/-- Discrete blow-up at a fixed step of an enstrophy trajectory. -/
def DiscreteBlowupAt
    (E : ℕ → ℝ) (nstar : ℕ) : Prop :=
  ∀ B : ℝ, E nstar > B

/-- Discrete breakdown means blow-up at some finite step. -/
def DiscreteBreakdown
    (E : ℕ → ℝ) : Prop :=
  ∃ nstar : ℕ, DiscreteBlowupAt E nstar

/-- An explicit Euclidean witness for discrete breakdown. -/
structure R3BreakdownWitness (K_max : ℕ) where
  pkg : R3ActualSolutionPackage K_max
  nstar : ℕ
  hblowup : DiscreteBlowupAt (r3EnstrophyTrajectory pkg) nstar

/-- The `R^3` breakdown predicate attached to an actual Euclidean solution
package. -/
def R3_breakdown_predicate
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) : Prop :=
  DiscreteBreakdown (r3EnstrophyTrajectory pkg)

/-- Unfolded form of `DiscreteBreakdown`. -/
theorem discreteBreakdown_iff
    (E : ℕ → ℝ) :
    DiscreteBreakdown E ↔ ∃ nstar : ℕ, DiscreteBlowupAt E nstar := by
  rfl

/-- Unfolded form of the Euclidean breakdown predicate. -/
theorem R3_breakdown_predicate_iff
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    R3_breakdown_predicate pkg
      ↔
    ∃ nstar : ℕ, DiscreteBlowupAt (r3EnstrophyTrajectory pkg) nstar := by
  rfl

/-- Every explicit `R^3` breakdown witness induces the abstract breakdown
predicate for its enstrophy trajectory. -/
theorem R3BreakdownWitness.to_discreteBreakdown
    {K_max : ℕ}
    (w : R3BreakdownWitness K_max) :
    R3_breakdown_predicate w.pkg := by
  exact ⟨w.nstar, w.hblowup⟩

end NSR3BreakdownDefinition
