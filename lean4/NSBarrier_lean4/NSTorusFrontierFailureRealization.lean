import NSBarrier.NSTorusBreakdownToFrontier
import Mathlib.Tactic

namespace NSTorusFrontierFailureRealization

open NSMillenniumFrontier
open NSTorusBreakdownDefinition
open NSTorusCounterexampleData
open NSTorusBreakdownToFrontier
open NSTorusSolutionPackage

/-- D4 realization theorem: the frontier failure isolated in D3 is not merely
an abstract contradiction statement. It is realized by an actual torus solution
package carrying a discrete breakdown witness. -/
theorem frontier_failure_realized_by_actual_torus_breakdown
    {K_max m : ℕ}
    (d : TorusBreakdownFrontierData K_max m) :
    ∃ pkg : TorusActualSolutionPackage K_max m,
      torus_breakdown_predicate pkg ∧
      (MillenniumFrontierHypothesis → False) := by
  refine ⟨d.counterexampleData.witness.pkg, ?_⟩
  refine ⟨torus_breakdown_of_counterexample_data d.counterexampleData, ?_⟩
  exact torus_breakdown_implies_frontier_failure d

end NSTorusFrontierFailureRealization
