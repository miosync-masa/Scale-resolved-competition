import NSBarrier.NSR3MinimalPDEFrontier
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3ActualSigmaBound

open NSR3MinimalPDEFrontier
open NSR3ShellActual
open NSR3NavierStokesFields

/-- Pointwise / a.e. actual sigma-bound data for the canonical Euclidean choice
`sigma = sigmaFromOpNormR3 Sop`. -/
structure R3ShellSigmaBoundProofData (K_max : ℕ) where
  Sop : Fin K_max → R3 → Mat3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_mem :
    ∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 Sop k) ⊤ μR3
  sigma_ae_bound :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μR3,
      ‖sigmaFromOpNormR3 Sop k x‖ ≤ strainSup

/-- Actual Euclidean sigma-bound theorem:
from `sigma_mem` plus an a.e. pointwise bound by `strainSup`,
obtain the required `L∞` control. -/
theorem sigma_bound_of_ae_bound_R3
    {K_max : ℕ}
    (sad : R3ShellSigmaBoundProofData K_max) :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (sigmaFromOpNormR3 sad.Sop k) (sad.sigma_mem k)‖ ≤ sad.strainSup := by
  intro k
  rw [MeasureTheory.Lp.norm_toLp (f := sigmaFromOpNormR3 sad.Sop k) (hf := sad.sigma_mem k)]
  have hleft_ne :
      MeasureTheory.eLpNorm (sigmaFromOpNormR3 sad.Sop k) ⊤ μR3 ≠ ⊤ :=
    ne_of_lt (sad.sigma_mem k).eLpNorm_lt_top
  have hle :
      MeasureTheory.eLpNormEssSup (sigmaFromOpNormR3 sad.Sop k) μR3
        ≤ ENNReal.ofReal sad.strainSup :=
    MeasureTheory.eLpNormEssSup_le_of_ae_bound (sad.sigma_ae_bound k)
  rw [MeasureTheory.eLpNorm_exponent_top] at hleft_ne ⊢
  calc
    (MeasureTheory.eLpNormEssSup (sigmaFromOpNormR3 sad.Sop k) μR3).toReal
      ≤ (ENNReal.ofReal sad.strainSup).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = sad.strainSup := ENNReal.toReal_ofReal sad.strainSup_nonneg

end NSR3ActualSigmaBound
