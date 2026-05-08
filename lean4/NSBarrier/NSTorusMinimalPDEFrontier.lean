import NSBarrier.NSTorusTrueFieldBridge
import NSBarrier.NSMinimalPDEFrontier
import NSBarrier.NSPDERegularityTheorems
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSTorusSmoothData
open NSTorusTrueFieldBridge
open NSActualSigmaBound
open NSMinimalPDEFrontier
open NSStrainRegularityTheorems
open NSPDERegularityTheorems

namespace NSTorusMinimalPDEFrontier

/-- Torus true-field data augmented with the shell fields needed to instantiate the minimal PDE
frontier theorems.

This is the point where the "true field" package and the "minimal frontier" package meet: the
full vorticity still comes from a smooth torus slice, while the shellwise vorticity fields are made
explicit so that the existing `NSMinimalPDEFrontier` theorems can be instantiated directly. -/
structure TorusTrueFieldMinimalPDEData (K_max : ℕ)
    extends TorusSmoothSolutionFieldData K_max where
  shellOmega : Fin K_max → T3 → Vec3
  shellOmega_mem :
    ∀ k : Fin K_max, MeasureTheory.MemLp (shellOmega k) (2 : ℝ≥0∞) μT3
  Sop_meas :
    ∀ k : Fin K_max, AEStronglyMeasurable (Sop k) μT3
  stretch_eq :
    ∀ k : Fin K_max, stretch k = fun x => (Sop k x) (shellOmega k x)
  stretch_dom_from_shell :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖(Sop k x) (shellOmega k x)‖ ≤ ‖sigmaFromOpNorm Sop k x • shellOmega k x‖

/-- The shell-independent sigma bound on `σ = ‖Sop‖op` yields the corresponding operator-norm
bound needed by `NSMinimalPDEFrontier`. -/
theorem Sop_ae_bound_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖d.Sop k x‖ ≤ d.strainSup := by
  intro k
  filter_upwards [d.sigma_ae_bound k] with x hx
  simpa [norm_sigmaFromOpNorm] using hx

/-- The canonical sigma field is measurable when the strain operator field is measurable. -/
theorem sigmaFromOpNorm_measurable_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    ∀ k : Fin K_max,
      AEStronglyMeasurable (sigmaFromOpNorm d.Sop k) μT3 :=
  sigmaFromOpNorm_aestronglyMeasurable_of_Sop d.Sop d.Sop_meas

/-- Instantiation of the minimal PDE frontier: true torus fields supply `sigma_mem` and the
shellwise `L²` stretching field. -/
theorem true_fields_imply_minimal_pde_frontier_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    (∀ k : Fin K_max,
      MemLp (sigmaFromOpNorm d.Sop k) ⊤ μT3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (d.Sop k x) (d.shellOmega k x)) (2 : ℝ≥0∞) μT3) := by
  constructor
  · exact
      sigma_mem_of_aestronglyMeasurable_and_ae_bound
        d.Sop d.strainSup
        (sigmaFromOpNorm_measurable_of_true_fields_T3 d)
        (Sop_ae_bound_of_true_fields_T3 d)
  · exact
      stretch_mem_of_first_principles
        d.Sop d.shellOmega d.strainSup
        (sigmaFromOpNorm_measurable_of_true_fields_T3 d)
        (Sop_ae_bound_of_true_fields_T3 d)
        d.shellOmega_mem
        (by
          intro k
          have hmeas : AEStronglyMeasurable (d.stretch k) μT3 :=
            (d.stretch_mem k).aestronglyMeasurable
          simpa [d.stretch_eq k] using hmeas)
        d.stretch_dom_from_shell

/-- The true torus fields induce the primitive PDE regularity package used by the paper-facing
surface in `NSPDERegularityTheorems`. -/
noncomputable def toPrimitiveStrainRegularityData_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    PrimitiveStrainRegularityData K_max where
  Sop := d.Sop
  vorticity := d.vorticity
  vorticity_mem := memLp_two_of_continuous d.vorticity_continuous
  shellOmega := d.shellOmega
  shellOmega_mem := d.shellOmega_mem
  strainSup := d.strainSup
  strainSup_nonneg := d.strainSup_nonneg
  Sop_ae_bound := Sop_ae_bound_of_true_fields_T3 d
  sigma_mem := (true_fields_imply_minimal_pde_frontier_T3 d).1
  stretch_mem := by
    intro k
    simpa [d.stretch_eq k] using (true_fields_imply_minimal_pde_frontier_T3 d).2 k

/-- Instantiation of the paper-facing PDE surface: `sigma_ae_bound` on `T³` true fields. -/
theorem sigma_ae_bound_derived_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖sigmaFromOpNorm d.Sop k x‖ ≤ d.strainSup := by
  simpa using
    (sigma_ae_bound_derived (toPrimitiveStrainRegularityData_of_true_fields_T3 d))

/-- Instantiation of the paper-facing PDE surface: `L∞` control of sigma on `T³` true fields. -/
theorem sigma_Linfty_bound_derived_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    ∀ k : Fin K_max,
      (eLpNorm (sigmaFromOpNorm d.Sop k) ⊤ μT3).toReal ≤ d.strainSup := by
  simpa using
    (sigma_Linfty_bound_derived (toPrimitiveStrainRegularityData_of_true_fields_T3 d))

/-- Instantiation of the paper-facing PDE surface: pointwise operator domination on `T³` true
fields. -/
theorem stretch_pointwise_dom_derived_of_true_fields_T3
    {K_max : ℕ}
    (d : TorusTrueFieldMinimalPDEData K_max) :
    ∀ k : Fin K_max, ∀ x : T3,
      ‖(d.Sop k x) (d.shellOmega k x)‖
        ≤ ‖d.Sop k x‖ * ‖d.shellOmega k x‖ := by
  simpa using
    (stretch_pointwise_dom_derived
      (toPrimitiveStrainRegularityData_of_true_fields_T3 d))

end NSTorusMinimalPDEFrontier
