import NSBarrier.NSTorusSolutionPackage
import Mathlib.Tactic

namespace NSTorusBreakdownDefinition

open NSTorusSolutionPackage

/-- Discrete blow-up of an enstrophy trajectory at a fixed step. -/
def DiscreteBlowupAt
    (E : ℕ → ℝ) (nstar : ℕ) : Prop :=
  ∀ B : ℝ, E nstar > B

/-- Discrete breakdown means blow-up at some finite step. -/
def DiscreteBreakdown
    (E : ℕ → ℝ) : Prop :=
  ∃ nstar : ℕ, DiscreteBlowupAt E nstar

/-- A torus-side witness for discrete breakdown, packaged directly on top of the
actual torus solution package. -/
structure TorusBreakdownWitness (K_max m : ℕ) where
  pkg : TorusActualSolutionPackage K_max m
  nstar : ℕ
  hblowup : DiscreteBlowupAt (torusEnstrophyTrajectory pkg) nstar

/-- The torus breakdown predicate attached to an actual torus solution package. -/
def torus_breakdown_predicate
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) : Prop :=
  DiscreteBreakdown (torusEnstrophyTrajectory pkg)

/-- Unfolded form of `DiscreteBreakdown`. -/
theorem discreteBreakdown_iff
    (E : ℕ → ℝ) :
    DiscreteBreakdown E ↔ ∃ nstar : ℕ, DiscreteBlowupAt E nstar := by
  rfl

/-- Unfolded form of the torus-side breakdown predicate. -/
theorem torus_breakdown_predicate_iff
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    torus_breakdown_predicate pkg
      ↔
    ∃ nstar : ℕ, DiscreteBlowupAt (torusEnstrophyTrajectory pkg) nstar := by
  rfl

/-- Every explicit torus-side breakdown witness induces the abstract breakdown
predicate for its enstrophy trajectory. -/
theorem TorusBreakdownWitness.to_discreteBreakdown
    {K_max m : ℕ}
    (w : TorusBreakdownWitness K_max m) :
    torus_breakdown_predicate w.pkg := by
  exact ⟨w.nstar, w.hblowup⟩

end NSTorusBreakdownDefinition
