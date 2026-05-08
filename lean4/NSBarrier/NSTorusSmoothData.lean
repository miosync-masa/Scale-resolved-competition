import NSBarrier.NSStrainOpVectorActual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual

namespace NSTorusSmoothData

/-- Initial vorticity data for the torus smooth-data branch.

At the present reduction level, the only property needed downstream is continuity:
compactness of `T³` then upgrades the field to `L²(T³)`. Any stronger smoothness package can
refine this structure later without changing the barrier-facing interface. -/
structure TorusSmoothInitialData where
  vorticity : T3 → Vec3
  vorticity_continuous : Continuous vorticity

/-- A continuous vector field on the compact torus belongs to `L²(T³)`. -/
theorem memLp_two_of_continuous
    {ω : T3 → Vec3}
    (hω : Continuous ω) :
    MemLp ω (2 : ℝ≥0∞) μT3 := by
  have hmeas : AEStronglyMeasurable ω μT3 :=
    hω.aestronglyMeasurable_of_compactSpace
  have hcompact : IsCompact (Set.range ω) :=
    isCompact_range hω
  have hbounded : Bornology.IsBounded (Set.range ω) :=
    hcompact.isBounded
  obtain ⟨C, hC⟩ := hbounded.subset_closedBall (0 : Vec3)
  refine MemLp.of_bound hmeas C ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hx : ω x ∈ Set.range ω := ⟨x, rfl⟩
  have hxC : ω x ∈ Metric.closedBall (0 : Vec3) C :=
    hC hx
  simpa [mem_closedBall_zero_iff] using hxC

/-- Smooth torus initial data enter the current PDE frontier through their `L²` vorticity
membership. The present proof uses only continuity and compactness. -/
theorem smooth_initial_data_implies_omega_mem_T3
    (d : TorusSmoothInitialData) :
    MemLp d.vorticity (2 : ℝ≥0∞) μT3 :=
  memLp_two_of_continuous d.vorticity_continuous

end NSTorusSmoothData
