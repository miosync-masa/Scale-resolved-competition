import NSBarrier.NSTorusFrontierFailureRealization
import Mathlib.Tactic

namespace NSTorusBreakdownExistence

open NSMillenniumFrontier
open NSTorusBreakdownDefinition
open NSTorusCounterexampleData
open NSTorusBreakdownToFrontier

/-- Final D-branch theorem.

At the current formalization level, the final counterexample statement is
packaged as the existence of torus-side smooth counterexample data whose
associated actual solution package satisfies the discrete breakdown predicate,
and whose existence forces failure of every millennium-frontier hypothesis. -/
theorem exists_torus_breakdown_counterexample
    {K_max m : ℕ}
    (d : TorusBreakdownFrontierData K_max m) :
    ∃ ce : TorusSmoothCounterexampleData K_max m,
      torus_breakdown_predicate ce.witness.pkg ∧
      (MillenniumFrontierHypothesis → False) := by
  refine ⟨d.counterexampleData, ?_⟩
  refine ⟨torus_breakdown_of_counterexample_data d.counterexampleData, ?_⟩
  exact torus_breakdown_implies_frontier_failure d

end NSTorusBreakdownExistence
