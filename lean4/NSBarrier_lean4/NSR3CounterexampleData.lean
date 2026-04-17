import NSBarrier.NSR3BreakdownDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3CounterexampleData

open NSR3ShellActual
open NSR3NavierStokesFields
open NSR3BreakdownDefinition

/-- Smooth initial data package for the Euclidean `R^3` counterexample branch.

Unlike the torus branch, continuity on `R^3` does not imply `L²`, so both the
continuity and the `L²` enstrophy input are stored explicitly. -/
structure R3SmoothInitialData where
  vorticity : R3 → Vec3
  vorticity_continuous : Continuous vorticity
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3

/-- Euclidean counterexample package: smooth initial data together with an
actual `R^3` breakdown witness for a solution package starting from that datum. -/
structure R3SmoothCounterexampleData (K_max : ℕ) where
  initialData : R3SmoothInitialData
  witness : R3BreakdownWitness K_max
  hinitial : witness.pkg.pdeData.vorticity = initialData.vorticity

/-- The packaged initial datum is smooth in the current Euclidean branch
sense. -/
theorem smooth_initial_data_of_counterexample_R3
    {K_max : ℕ}
    (d : R3SmoothCounterexampleData K_max) :
    Continuous d.initialData.vorticity :=
  d.initialData.vorticity_continuous

/-- The packaged Euclidean initial datum supplies the `L²(R^3)` frontier input
used elsewhere in the `R^3` branch. -/
theorem initial_vorticity_mem_of_counterexample_R3
    {K_max : ℕ}
    (d : R3SmoothCounterexampleData K_max) :
    MemLp d.initialData.vorticity (2 : ℝ≥0∞) μR3 :=
  d.initialData.vorticity_mem

/-- The explicit witness gives the Euclidean breakdown predicate for the
packaged actual solution package. -/
theorem R3_breakdown_of_counterexample_data
    {K_max : ℕ}
    (d : R3SmoothCounterexampleData K_max) :
    R3_breakdown_predicate d.witness.pkg :=
  d.witness.to_discreteBreakdown

/-- C6 wrapper theorem: an Euclidean counterexample package provides

1. smooth initial data,
2. the corresponding `L²(R^3)` vorticity input,
3. an `R^3`-side discrete breakdown witness

for one and the same actual solution package. -/
theorem R3_counterexample_data
    {K_max : ℕ}
    (d : R3SmoothCounterexampleData K_max) :
    ∃ data : R3SmoothInitialData,
      data.vorticity = d.witness.pkg.pdeData.vorticity ∧
      Continuous data.vorticity ∧
      MemLp data.vorticity (2 : ℝ≥0∞) μR3 ∧
      R3_breakdown_predicate d.witness.pkg := by
  refine ⟨d.initialData, d.hinitial.symm, d.initialData.vorticity_continuous, ?_, ?_⟩
  · exact initial_vorticity_mem_of_counterexample_R3 d
  · exact R3_breakdown_of_counterexample_data d

end NSR3CounterexampleData
