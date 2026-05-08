import NSBarrier.NSNavierStokesProjectedCore
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData T3)
open NSStrainOpVectorActual
open NSNavierStokesLpCore
open NSNavierStokesProjectedCore
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSNavierStokesFields

-- ============================================================
-- SECTION 1: FUNCTION-LEVEL ACTUAL FIELD DATA
-- ============================================================

/-- Actual field-level Navier–Stokes data on `T³`, reduced to the two
    remaining PDE-facing obligations:

  1. `sigma_bound`:
       the scalar amplitude proxy is bounded by `strainSup` in `L∞`;
  2. `stretch_dom`:
       the actual stretching output is dominated in `L²` by the scalar-multiplied
       shell-projected vorticity field.

The shell-projected vorticity itself is no longer a field:
it is defined canonically by the projector family. -/
structure NavierStokesProjectedFieldData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticity : T3 → Vec3
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  sigma : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3

  stretch : Fin K_max → T3 → Vec3
  stretch_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (stretch k) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- The scalar amplitude proxy is bounded by `strainSup` in `L∞`. -/
  sigma_bound :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (sigma k) (sigma_mem k)‖ ≤ strainSup

  /-- The actual stretching field is dominated in `L²` by the scalar-multiplied
      shell-projected vorticity field. -/
  stretch_dom :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (stretch k) (stretch_mem k)‖ ≤
        ‖(MeasureTheory.MemLp.toLp (sigma k) (sigma_mem k)) •
          (projData.Pk k (MeasureTheory.MemLp.toLp vorticity vorticity_mem))‖

#check @NavierStokesProjectedFieldData

-- ============================================================
-- SECTION 2: BRIDGE TO THE PROJECTED Lp CORE
-- ============================================================

/-- Convert function-level actual field data into the projected `Lp` core
    used by the already-proved abstract/actual A1 chain. -/
noncomputable def toProjectedLpCoreData
    {K_max : ℕ}
    (ns : NavierStokesProjectedFieldData K_max) :
    NavierStokesProjectedLpCoreData K_max where
  projData := ns.projData
  vorticityLp := MeasureTheory.MemLp.toLp ns.vorticity ns.vorticity_mem
  sigmaLp := fun k => MeasureTheory.MemLp.toLp (ns.sigma k) (ns.sigma_mem k)
  stretchLp := fun k => MeasureTheory.MemLp.toLp (ns.stretch k) (ns.stretch_mem k)
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  stretch_dom := ns.stretch_dom

#check @toProjectedLpCoreData

-- ============================================================
-- SECTION 3: CONSEQUENCES
-- ============================================================

/-- The function-level actual field data already yield
    `LocalizedProjectedStretching`. -/
theorem localizedProjectedStretching_of_field_data
    {K_max : ℕ}
    (ns : NavierStokesProjectedFieldData K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData (toLpCoreData (toProjectedLpCoreData ns))))
      (strainState (toLpCoreData (toProjectedLpCoreData ns)))
      (toGradientAmplitude (localizedData (toLpCoreData (toProjectedLpCoreData ns)))) := by
  exact
    NSNavierStokesProjectedCore.localizedProjectedStretching_of_projected_core
      (toProjectedLpCoreData ns)

/-- Gradient control by strain holds with constant `1`
    for the function-level actual field data. -/
theorem gradientControlledByStrain_of_field_data
    {K_max : ℕ}
    (ns : NavierStokesProjectedFieldData K_max) :
    GradientControlledByStrain
      (strainState (toLpCoreData (toProjectedLpCoreData ns)))
      (toGradientAmplitude (localizedData (toLpCoreData (toProjectedLpCoreData ns))))
      1 := by
  exact
    NSNavierStokesProjectedCore.gradientControlledByStrain_of_projected_core
      (toProjectedLpCoreData ns)

/-- The function-level actual field data already suffice to yield the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_field_data
    {K_max : ℕ}
    (ns : NavierStokesProjectedFieldData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData (toLpCoreData (toProjectedLpCoreData ns))))
      (strainState (toLpCoreData (toProjectedLpCoreData ns))) := by
  exact
    NSNavierStokesProjectedCore.productionFromStrainSup_of_projected_core
      (toProjectedLpCoreData ns)

-- The packaged shell field is, by definition in the projected core, the actual shell
-- projector applied to the full vorticity field.
theorem shellOmegaLp_eq_projector_of_field_data
    {K_max : ℕ}
    (ns : NavierStokesProjectedFieldData K_max)
    (k : Fin K_max) :
    shellOmegaLp (toProjectedLpCoreData ns) k =
      ns.projData.Pk k (MeasureTheory.MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  exact NSNavierStokesProjectedCore.shellOmegaLp_eq_projector (toProjectedLpCoreData ns) k

#check @localizedProjectedStretching_of_field_data
#check @gradientControlledByStrain_of_field_data
#check @productionFromStrainSup_of_field_data
#check @shellOmegaLp_eq_projector_of_field_data

end NSNavierStokesFields
