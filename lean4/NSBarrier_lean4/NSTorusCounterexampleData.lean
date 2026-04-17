import NSBarrier.NSTorusBreakdownDefinition
import NSBarrier.NSStrainOpVectorActual
import NSBarrier.NSTorusShellActual
import NSBarrier.NSTorusSmoothData
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual

namespace NSTorusCounterexampleData

open NSTorusSmoothData
open NSTorusBreakdownDefinition

/-- T³ counterexample data package.

This keeps together:
1. a smooth torus initial datum;
2. an actual torus solution package built from that datum;
3. a discrete breakdown witness for the associated enstrophy trajectory.

The equality `hinitial` is the bookkeeping bridge ensuring that the packaged
breakdown witness really starts from the chosen smooth initial datum. -/
structure TorusSmoothCounterexampleData (K_max m : ℕ) where
  initialData : TorusSmoothInitialData
  witness : TorusBreakdownWitness K_max m
  hinitial : witness.pkg.localData.initialData = initialData

/-- The packaged initial datum is smooth in the sense currently formalized in
the T³ branch. -/
theorem smooth_initial_data_of_counterexample
    {K_max m : ℕ}
    (d : TorusSmoothCounterexampleData K_max m) :
    Continuous d.initialData.vorticity :=
  d.initialData.vorticity_continuous

/-- The packaged smooth initial datum supplies the same `L²(T³)` frontier input
used elsewhere in the torus branch. -/
theorem initial_vorticity_mem_of_counterexample
    {K_max m : ℕ}
    (d : TorusSmoothCounterexampleData K_max m) :
    MemLp d.initialData.vorticity (2 : ℝ≥0∞) NSStrainOpVectorActual.μT3 :=
  smooth_initial_data_implies_omega_mem_T3 d.initialData

/-- The explicit witness gives the torus breakdown predicate for the packaged
actual solution package. -/
theorem torus_breakdown_of_counterexample_data
    {K_max m : ℕ}
    (d : TorusSmoothCounterexampleData K_max m) :
    torus_breakdown_predicate d.witness.pkg :=
  d.witness.to_discreteBreakdown

/-- Current D2 wrapper theorem: a torus counterexample package provides

1. smooth initial data,
2. the corresponding `L²(T³)` vorticity input,
3. a torus-side discrete breakdown witness

for one and the same actual solution package. -/
theorem smooth_counterexample_data_T3
    {K_max m : ℕ}
    (d : TorusSmoothCounterexampleData K_max m) :
    ∃ data : TorusSmoothInitialData,
      data = d.witness.pkg.localData.initialData ∧
      Continuous data.vorticity ∧
      MemLp data.vorticity (2 : ℝ≥0∞) NSStrainOpVectorActual.μT3 ∧
      torus_breakdown_predicate d.witness.pkg := by
  refine ⟨d.initialData, d.hinitial.symm, d.initialData.vorticity_continuous, ?_, ?_⟩
  · exact initial_vorticity_mem_of_counterexample d
  · exact torus_breakdown_of_counterexample_data d

end NSTorusCounterexampleData
