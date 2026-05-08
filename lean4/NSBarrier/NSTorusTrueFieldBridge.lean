import NSBarrier.NSTorusSmoothData
import NSBarrier.NSActualTrueFields
import NSBarrier.NSActualSigmaBound
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData)
open NSTorusShellActual
open NSStrainOpVectorActual
open NSTorusSmoothData
open NSActualSigmaBound
open NSActualTrueFields
open NSNavierStokesFields
open NSNavierStokesLpCore
open NSNavierStokesProjectedCore
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSTorusTrueFieldBridge

/-- Torus smooth-solution slice data, packaged so it can be fed into the true-field bridge.

Compared with `NavierStokesTrueFieldData`, the only field internalized here is the `L²`
membership of the full vorticity: on the compact torus this follows from continuity. The other
analytic obligations remain explicit. -/
structure TorusSmoothSolutionFieldData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticity : NSTorusShellActual.T3 → Vec3
  vorticity_continuous : Continuous vorticity

  Sop : Fin K_max → NSTorusShellActual.T3 → Mat3

  stretch : Fin K_max → NSTorusShellActual.T3 → Vec3
  stretch_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (stretch k) (2 : ℝ≥0∞) μT3

  sigmaOmega : Fin K_max → NSTorusShellActual.T3 → Vec3
  sigmaOmega_mem :
    ∀ k : Fin K_max, MeasureTheory.MemLp (sigmaOmega k) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  sigma_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (sigmaFromOpNorm Sop k) ⊤ μT3

  sigma_ae_bound :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖sigmaFromOpNorm Sop k x‖ ≤ strainSup

  sigmaOmega_lp_eq :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (sigmaOmega k) (sigmaOmega_mem k)
        =
      (MeasureTheory.MemLp.toLp (sigmaFromOpNorm Sop k) (sigma_mem k)) •
        (projData.Pk k (MeasureTheory.MemLp.toLp vorticity
          (memLp_two_of_continuous vorticity_continuous)))

  stretch_ae_dom :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖stretch k x‖ ≤ ‖sigmaOmega k x‖

/-- A smooth torus solution slice supplies the true actual field data needed by the downstream
PDE-facing bridge. -/
noncomputable def smooth_solution_implies_true_field_data_T3
    {K_max : ℕ}
    (d : TorusSmoothSolutionFieldData K_max) :
    NavierStokesTrueFieldData K_max where
  projData := d.projData
  vorticity := d.vorticity
  vorticity_mem := memLp_two_of_continuous d.vorticity_continuous
  Sop := d.Sop
  stretch := d.stretch
  stretch_mem := d.stretch_mem
  sigmaOmega := d.sigmaOmega
  sigmaOmega_mem := d.sigmaOmega_mem
  strainSup := d.strainSup
  strainSup_nonneg := d.strainSup_nonneg
  sigma_mem := d.sigma_mem
  sigma_ae_bound := d.sigma_ae_bound
  sigmaOmega_lp_eq := d.sigmaOmega_lp_eq
  stretch_ae_dom := d.stretch_ae_dom

/-- Therefore a smooth torus solution slice already yields the projected field data used by the
barrier-facing chain. -/
noncomputable def projected_field_data_of_smooth_solution_T3
    {K_max : ℕ}
    (d : TorusSmoothSolutionFieldData K_max) :
    NavierStokesProjectedFieldData K_max :=
  toNavierStokesProjectedFieldData
    (smooth_solution_implies_true_field_data_T3 d)

/-- Therefore a smooth torus solution slice already yields the abstract
`ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_smooth_solution_T3
    {K_max : ℕ}
    (d : TorusSmoothSolutionFieldData K_max) :
    let core := toLpCoreData (toProjectedLpCoreData
      (projected_field_data_of_smooth_solution_T3 d))
    ProductionFromStrainSup
      (localizedProduction (localizedData core))
      (strainState core) := by
  exact
    productionFromStrainSup_of_true_fields
      (smooth_solution_implies_true_field_data_T3 d)

end NSTorusTrueFieldBridge
