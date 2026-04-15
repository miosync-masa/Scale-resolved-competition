import NSBarrier.NSActualSigmaBound
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSActualSigmaBound

namespace NSActualSigmaBoundProof

/-- Pointwise / a.e. actual sigma-bound data for the canonical choice
    `sigma = sigmaFromOpNorm Sop`. -/
structure ShellSigmaBoundProofData (K_max : ℕ) where
  Sop : Fin K_max → T3 → Mat3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- The canonical sigma field belongs to `L∞(T³)`. -/
  sigma_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (sigmaFromOpNorm Sop k) ⊤ μT3

  /-- Pointwise / a.e. domination by the shell-independent amplitude. -/
  sigma_ae_bound :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖sigmaFromOpNorm Sop k x‖ ≤ strainSup

#check @ShellSigmaBoundProofData

/-- Actual sigma-bound theorem:
    from `sigma_mem` plus an a.e. pointwise bound by `strainSup`,
    obtain the required `L∞` control. -/
theorem sigma_bound_of_ae_bound
    {K_max : ℕ}
    (sad : ShellSigmaBoundProofData K_max) :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigmaFromOpNorm sad.Sop k) ⊤ μT3).toReal ≤ sad.strainSup := by
  intro k
  have hleft_ne :
      MeasureTheory.eLpNorm (sigmaFromOpNorm sad.Sop k) ⊤ μT3 ≠ ⊤ :=
    ne_of_lt (sad.sigma_mem k).eLpNorm_lt_top
  have hle :
      MeasureTheory.eLpNormEssSup (sigmaFromOpNorm sad.Sop k) μT3
        ≤ ENNReal.ofReal sad.strainSup :=
    MeasureTheory.eLpNormEssSup_le_of_ae_bound (sad.sigma_ae_bound k)
  rw [MeasureTheory.eLpNorm_exponent_top] at hleft_ne ⊢
  calc (MeasureTheory.eLpNormEssSup (sigmaFromOpNorm sad.Sop k) μT3).toReal
      _ ≤ (ENNReal.ofReal sad.strainSup).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = sad.strainSup := ENNReal.toReal_ofReal sad.strainSup_nonneg

#check @sigma_bound_of_ae_bound

/-- Build the sigma-core data needed by the downstream actual chain. -/
noncomputable def toShellStrainOperatorSigmaCoreData
    {K_max : ℕ}
    (sad : ShellSigmaBoundProofData K_max)
    (omega : Fin K_max → T3 → Vec3)
    (omega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (omega k) (2 : ℝ≥0∞) μT3)
    (Z_mem :
      ∀ k : Fin K_max,
        MeasureTheory.MemLp (fun x => (sad.Sop k x) (omega k x)) (2 : ℝ≥0∞) μT3) :
    ShellStrainOperatorSigmaCoreData K_max where
  Sop := sad.Sop
  omega := omega
  omega_mem := omega_mem
  Z_mem := Z_mem
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  sigma_mem := sad.sigma_mem
  sigma_bound := sigma_bound_of_ae_bound sad

#check @toShellStrainOperatorSigmaCoreData

end NSActualSigmaBoundProof
