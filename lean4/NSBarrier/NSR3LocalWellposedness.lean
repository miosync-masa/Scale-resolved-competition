import NSBarrier.NSGalerkinExistenceTheorems
import NSBarrier.NSR3NavierStokesFields
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSGalerkinExistenceTheorems

namespace NSR3LocalWellposedness

open NSR3ShellActual
open NSR3NavierStokesFields

/-- Euclidean local wellposedness input package.

This is the `R³` analogue of `NSTorusLocalWellposednessData`. Since continuity
on `R³` does not force `L²`, we store the `L²(R³)` hypothesis explicitly
together with the local Picard-Lindelöf seed data. -/
structure R3LocalWellposednessData (m : ℕ) where
  vorticity : R3 → Vec3
  vorticity_continuous : Continuous vorticity
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3
  spec : GalerkinODESpec m
  T0 : ℝ
  hT0 : 0 < T0
  a : NNReal
  L : NNReal
  K : NNReal
  hPL :
    IsPicardLindelof
      spec.rhs
      (show Set.Icc (0 : ℝ) T0 from ⟨0, by constructor <;> linarith⟩)
      spec.state₀
      a 0 L K

/-- The packaged Euclidean initial datum already supplies the `L²(R³)` input
used by the frontier layers. -/
theorem initial_vorticity_mem_of_R3_local_wellposedness
    {m : ℕ}
    (d : R3LocalWellposednessData m) :
    MemLp d.vorticity (2 : ℝ≥0∞) μR3 :=
  d.vorticity_mem

/-- The finite-dimensional Picard-Lindelöf package yields the local existence
seed used by later continuation layers. -/
noncomputable def localExistenceSeed_of_R3_local_wellposedness
    {m : ℕ}
    (d : R3LocalWellposednessData m) :
    LocalExistenceSeed m d.spec :=
  localExistenceSeed_of_picardLindelof
    m d.spec d.T0 d.hT0 d.hPL

/-- Current Euclidean local-seed wrapper: the packaged initial vorticity gives
the `L²(R³)` frontier input, and the associated Galerkin Picard-Lindelöf data
give a local existence seed on `[0, T0]`. -/
theorem smooth_local_solution_seed_on_R3
    {m : ℕ}
    (d : R3LocalWellposednessData m) :
    ∃ seed : LocalExistenceSeed m d.spec,
      seed.T0 = d.T0 ∧
      MemLp d.vorticity (2 : ℝ≥0∞) μR3 := by
  refine ⟨localExistenceSeed_of_R3_local_wellposedness d, rfl, ?_⟩
  exact initial_vorticity_mem_of_R3_local_wellposedness d

end NSR3LocalWellposedness
