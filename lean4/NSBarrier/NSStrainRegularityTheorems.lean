import NSBarrier.NSActualTrueFields
import NSBarrier.NSActualSigmaBoundProof
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSActualSigmaBound
open NSActualSigmaBoundProof

namespace NSStrainRegularityTheorems

/-- Primitive strain regularity data. -/
structure PrimitiveStrainRegularityData (K_max : ℕ) where
  Sop : Fin K_max → T3 → Mat3
  vorticity : T3 → Vec3
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μT3
  shellOmega : Fin K_max → T3 → Vec3
  shellOmega_mem : ∀ k, MemLp (shellOmega k) (2 : ℝ≥0∞) μT3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  Sop_ae_bound : ∀ k, ∀ᵐ x ∂ μT3, ‖Sop k x‖ ≤ strainSup
  sigma_mem : ∀ k, MemLp (sigmaFromOpNorm Sop k) ⊤ μT3
  stretch_mem : ∀ k, MemLp (fun x => (Sop k x) (shellOmega k x)) (2 : ℝ≥0∞) μT3

#check @PrimitiveStrainRegularityData

theorem sigma_ae_bound_of_true_strain_operator_bound
    {K_max : ℕ}
    (d : PrimitiveStrainRegularityData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖sigmaFromOpNorm d.Sop k x‖ ≤ d.strainSup := by
  intro k
  filter_upwards [d.Sop_ae_bound k] with x hx
  rw [norm_sigmaFromOpNorm]
  exact hx

theorem sigma_mem_of_true_strain_regularity
    {K_max : ℕ}
    (d : PrimitiveStrainRegularityData K_max) :
    ∀ k : Fin K_max, MemLp (sigmaFromOpNorm d.Sop k) ⊤ μT3 :=
  d.sigma_mem

theorem sigma_Linfty_bound_of_true_strain_operator_bound
    {K_max : ℕ}
    (d : PrimitiveStrainRegularityData K_max) :
    ∀ k : Fin K_max,
      (eLpNorm (sigmaFromOpNorm d.Sop k) ⊤ μT3).toReal ≤ d.strainSup :=
  sigma_bound_of_ae_bound
    { Sop := d.Sop
      strainSup := d.strainSup
      strainSup_nonneg := d.strainSup_nonneg
      sigma_mem := d.sigma_mem
      sigma_ae_bound := sigma_ae_bound_of_true_strain_operator_bound d }

theorem stretch_mem_of_true_vorticity_transport
    {K_max : ℕ}
    (d : PrimitiveStrainRegularityData K_max) :
    ∀ k : Fin K_max,
      MemLp (fun x => (d.Sop k x) (d.shellOmega k x)) (2 : ℝ≥0∞) μT3 :=
  d.stretch_mem

theorem stretch_pointwise_dom_of_operator_norm
    {K_max : ℕ}
    (d : PrimitiveStrainRegularityData K_max) :
    ∀ k : Fin K_max, ∀ x : T3,
      ‖(d.Sop k x) (d.shellOmega k x)‖
        ≤ ‖d.Sop k x‖ * ‖d.shellOmega k x‖ :=
  fun k x => (d.Sop k x).le_opNorm (d.shellOmega k x)

#check @sigma_ae_bound_of_true_strain_operator_bound
#check @sigma_mem_of_true_strain_regularity
#check @sigma_Linfty_bound_of_true_strain_operator_bound
#check @stretch_mem_of_true_vorticity_transport
#check @stretch_pointwise_dom_of_operator_norm

end NSStrainRegularityTheorems
