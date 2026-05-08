import NSBarrier.NSR3FrontierFailureRealization
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3BreakdownExistence

open NSMillenniumFrontier
open NSR3BreakdownDefinition
open NSR3CounterexampleData
open NSR3BreakdownToFrontier

/-- E6 decision: the `R^3` branch is now presented at the same final theorem
surface level as the torus D5 endpoint. The core conclusion isolates only the
actual breakdown witness and the resulting frontier failure. -/
def R3CounterexampleConclusion
    {K_max : ℕ}
    (ce : R3SmoothCounterexampleData K_max) : Prop :=
  R3_breakdown_predicate ce.witness.pkg ∧
    (MillenniumFrontierHypothesis → False)

/-- Auxiliary Euclidean regularity facts carried by the same counterexample
package. These remain available as a stronger companion statement without
cluttering the D5-style final theorem surface. -/
def R3CounterexampleRegularityConclusion
    {K_max : ℕ}
    (ce : R3SmoothCounterexampleData K_max) : Prop :=
    Continuous ce.initialData.vorticity ∧
    MeasureTheory.MemLp ce.initialData.vorticity (2 : ℝ≥0∞) NSR3ShellActual.μR3

/-- Final C-branch theorem.

At the current Euclidean formalization level, the `R^3` counterexample
statement is packaged as the existence of smooth initial data together with an
actual Euclidean solution package whose discrete enstrophy trajectory satisfies
the breakdown predicate and whose existence forces failure of every
millennium-frontier hypothesis. This matches the torus D5 theorem surface. -/
theorem exists_breakdown_counterexample_R3
    {K_max : ℕ}
    (d : R3BreakdownFrontierData K_max) :
    ∃ ce : R3SmoothCounterexampleData K_max,
      R3CounterexampleConclusion ce := by
  refine ⟨d.counterexampleData, ?_⟩
  refine ⟨R3_breakdown_of_counterexample_data d.counterexampleData, ?_⟩
  exact R3_breakdown_implies_frontier_failure d

/-- Stronger Euclidean companion theorem: the same final counterexample package
also retains the explicit continuity and `L²(R³)` input facts used by the
PDE-facing side of the branch. -/
theorem exists_breakdown_counterexample_R3_with_regularity
    {K_max : ℕ}
    (d : R3BreakdownFrontierData K_max) :
    ∃ ce : R3SmoothCounterexampleData K_max,
      R3CounterexampleConclusion ce ∧
      R3CounterexampleRegularityConclusion ce := by
  refine ⟨d.counterexampleData, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨R3_breakdown_of_counterexample_data d.counterexampleData, ?_⟩
    exact R3_breakdown_implies_frontier_failure d
  · refine ⟨smooth_initial_data_of_counterexample_R3 d.counterexampleData, ?_⟩
    exact initial_vorticity_mem_of_counterexample_R3 d.counterexampleData

end NSR3BreakdownExistence
