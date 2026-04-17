import NSBarrier.NSR3ActualSigmaBound
import NSBarrier.NSR3ProjectorShellEquality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3ActualTrueFields

open NSR3ActualSigmaBound
open NSR3MinimalPDEFrontier
open NSR3ProjectorShellEquality
open NSR3ShellActual

/-- Genuine actual true-field data on `R³`.

This is the Euclidean analogue of the torus-side actual true-field package:
the shell fields are explicit functions, the shell projector family is the actual
Euclidean multiplier from Phase E1, and the scalar amplitude is canonically
`sigmaFromOpNormR3 Sop`. -/
structure R3NavierStokesTrueFieldData (K_max : ℕ) where
  vorticity : R3 → NSR3NavierStokesFields.Vec3
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3

  shellOmega : Fin K_max → R3 → NSR3NavierStokesFields.Vec3
  shellOmega_mem : ∀ k : Fin K_max, MemLp (shellOmega k) (2 : ℝ≥0∞) μR3

  Sop : Fin K_max → R3 → NSR3NavierStokesFields.Mat3
  Sop_meas : ∀ k : Fin K_max, AEStronglyMeasurable (Sop k) μR3

  stretch : Fin K_max → R3 → NSR3NavierStokesFields.Vec3
  stretch_mem : ∀ k : Fin K_max, MemLp (stretch k) (2 : ℝ≥0∞) μR3

  sigmaOmegaLp : Fin K_max → NSR3NavierStokesFields.L2VecR3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  sigma_mem :
    ∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 Sop k) ⊤ μR3
  sigma_ae_bound :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μR3,
      ‖sigmaFromOpNormR3 Sop k x‖ ≤ strainSup

  sigmaOmegaLp_eq :
    ∀ k : Fin K_max,
      sigmaOmegaLp k =
        (MemLp.toLp (sigmaFromOpNormR3 Sop k) (sigma_mem k)) •
          (NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
            (MemLp.toLp vorticity vorticity_mem))

  stretch_dom :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (stretch k) (stretch_mem k)‖ ≤ ‖sigmaOmegaLp k‖

  shellOmega_eq_proj :
    ∀ k : Fin K_max,
      MemLp.toLp (shellOmega k) (shellOmega_mem k)
        =
      NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
        (MemLp.toLp vorticity vorticity_mem)

  stretch_eq :
    ∀ k : Fin K_max,
      stretch k = fun x => (Sop k x) (shellOmega k x)

/-- The canonical Euclidean sigma field is bounded by `strainSup` in `L∞`. -/
theorem sigma_Linfty_bound_of_true_fields_R3
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (sigmaFromOpNormR3 ns.Sop k) (ns.sigma_mem k)‖ ≤ ns.strainSup := by
  exact sigma_bound_of_ae_bound_R3
    { Sop := ns.Sop
      strainSup := ns.strainSup
      strainSup_nonneg := ns.strainSup_nonneg
      sigma_mem := ns.sigma_mem
      sigma_ae_bound := ns.sigma_ae_bound }

/-- The shell-independent sigma bound yields the corresponding operator-norm
bound needed by the primitive Euclidean frontier package. -/
theorem Sop_ae_bound_of_true_fields_R3_actual
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μR3,
      ‖ns.Sop k x‖ ≤ ns.strainSup := by
  intro k
  filter_upwards [ns.sigma_ae_bound k] with x hx
  simpa [norm_sigmaFromOpNormR3] using hx

/-- Pointwise operator domination by the canonical Euclidean sigma field. -/
theorem stretch_dom_from_shell_of_true_fields_R3_actual
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μR3,
      ‖(ns.Sop k x) (ns.shellOmega k x)‖
        ≤ ‖sigmaFromOpNormR3 ns.Sop k x • ns.shellOmega k x‖ := by
  intro k
  refine Filter.Eventually.of_forall ?_
  intro x
  calc
    ‖(ns.Sop k x) (ns.shellOmega k x)‖
      ≤ ‖ns.Sop k x‖ * ‖ns.shellOmega k x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖sigmaFromOpNormR3 ns.Sop k x‖ * ‖ns.shellOmega k x‖ := by
      simp [norm_sigmaFromOpNormR3]
    _ = ‖sigmaFromOpNormR3 ns.Sop k x • ns.shellOmega k x‖ := by
      rw [norm_smul]

/-- Forget the explicit shell fields and feed the remaining data into the
actual Euclidean projected-field interface. -/
noncomputable def toR3ActualProjectedFieldData
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    R3ActualProjectedFieldData K_max where
  vorticity := ns.vorticity
  vorticity_mem := ns.vorticity_mem
  shellOmega := ns.shellOmega
  shellOmega_mem := ns.shellOmega_mem
  sigma := sigmaFromOpNormR3 ns.Sop
  sigma_mem := ns.sigma_mem
  sigmaOmegaLp := ns.sigmaOmegaLp
  stretch := ns.stretch
  stretch_mem := ns.stretch_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := sigma_Linfty_bound_of_true_fields_R3 ns
  stretch_dom := ns.stretch_dom
  shellOmega_eq_proj := ns.shellOmega_eq_proj

/-- The actual Euclidean true fields induce the primitive PDE-regularity package
used by the existing `NSR3MinimalPDEFrontier` theorems. -/
noncomputable def toPrimitiveR3StrainRegularityData_of_true_fields_R3
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    PrimitiveR3StrainRegularityData K_max where
  Sop := ns.Sop
  vorticity := ns.vorticity
  vorticity_mem := ns.vorticity_mem
  shellOmega := ns.shellOmega
  shellOmega_mem := ns.shellOmega_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  Sop_meas := ns.Sop_meas
  Sop_ae_bound := Sop_ae_bound_of_true_fields_R3_actual ns
  stretch := ns.stretch
  stretch_mem := ns.stretch_mem
  stretch_eq := ns.stretch_eq
  stretch_dom_from_shell := stretch_dom_from_shell_of_true_fields_R3_actual ns

/-- Actual Euclidean true fields satisfy the primitive minimal PDE frontier. -/
theorem true_fields_imply_minimal_pde_frontier_R3_actual
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    (∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 ns.Sop k) ⊤ μR3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (ns.Sop k x) (ns.shellOmega k x)) (2 : ℝ≥0∞) μR3) := by
  simpa using
    NSR3MinimalPDEFrontier.true_fields_imply_minimal_pde_frontier_R3
      (toPrimitiveR3StrainRegularityData_of_true_fields_R3 ns)

end NSR3ActualTrueFields
