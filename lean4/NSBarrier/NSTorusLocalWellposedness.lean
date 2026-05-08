import NSBarrier.NSTorusSmoothData
import NSBarrier.NSGalerkinExistenceTheorems
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSTorusSmoothData
open NSGalerkinExistenceTheorems

namespace NSTorusLocalWellposedness

/-- Torus-side local wellposedness input package.

The current development separates two ingredients:
1. the torus PDE input, represented here by smooth initial vorticity data;
2. the finite-dimensional Picard-Lindelöf seed used by the continuation layers.

This structure records them together without yet formalizing the full PDE-level map from the
smooth torus field to the Galerkin coordinate vector. -/
structure TorusLocalWellposednessData (m : ℕ) where
  initialData : TorusSmoothInitialData
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

/-- The smooth torus initial datum already supplies the `L²(T³)` vorticity hypothesis used by the
downstream PDE frontier. -/
theorem initial_vorticity_mem_of_torus_local_wellposedness
    {m : ℕ}
    (d : TorusLocalWellposednessData m) :
    MemLp d.initialData.vorticity (2 : ℝ≥0∞) μT3 :=
  smooth_initial_data_implies_omega_mem_T3 d.initialData

/-- The finite-dimensional Picard-Lindelöf package yields the local existence seed used by the
continuation and no-blowup layers. -/
noncomputable def localExistenceSeed_of_torus_local_wellposedness
    {m : ℕ}
    (d : TorusLocalWellposednessData m) :
    LocalExistenceSeed m d.spec :=
  localExistenceSeed_of_picardLindelof
    m d.spec d.T0 d.hT0 d.hPL

/-- Current torus local-seed wrapper: smooth initial vorticity gives the `L²` frontier input, and
the associated Galerkin Picard-Lindelöf package gives a local existence seed on `[0, T0]`. -/
theorem smooth_local_solution_seed_on_T3
    {m : ℕ}
    (d : TorusLocalWellposednessData m) :
    ∃ seed : LocalExistenceSeed m d.spec,
      seed.T0 = d.T0 ∧
      MemLp d.initialData.vorticity (2 : ℝ≥0∞) μT3 := by
  refine ⟨localExistenceSeed_of_torus_local_wellposedness d, rfl, ?_⟩
  exact initial_vorticity_mem_of_torus_local_wellposedness d

end NSTorusLocalWellposedness
