import NSBarrier.NSR3BreakdownToFrontier
import Mathlib.Tactic

namespace NSR3FrontierFailureRealization

open NSMillenniumFrontier
open NSR3BreakdownDefinition
open NSR3CounterexampleData
open NSR3BreakdownToFrontier
open NSR3SolutionPackage

/-- E5 realization theorem: the frontier failure isolated by the Euclidean
breakdown-to-frontier bridge is realized by an actual `R^3` solution package
carrying a discrete breakdown witness. -/
theorem frontier_failure_realized_by_actual_R3_breakdown
    {K_max : ℕ}
    (d : R3BreakdownFrontierData K_max) :
    ∃ pkg : NSR3BreakdownDefinition.R3ActualSolutionPackage K_max,
      R3_breakdown_predicate pkg ∧
      (MillenniumFrontierHypothesis → False) := by
  refine ⟨d.counterexampleData.witness.pkg, ?_⟩
  refine ⟨R3_breakdown_of_counterexample_data d.counterexampleData, ?_⟩
  exact R3_breakdown_implies_frontier_failure d

end NSR3FrontierFailureRealization
