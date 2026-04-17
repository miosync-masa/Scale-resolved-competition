import NSBarrier.NSR3LittlewoodPaleyActual
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3ProjectorContraction

open NSR3LittlewoodPaleyActual
open NSR3ShellActual

/-- The actual Euclidean shell projector is contractive on `L²(R³)^3`. -/
theorem actualR3ShellProjFamily_contraction
    {K_max : ℕ}
    (k : Fin K_max) (f : L2VecR3) :
    ‖actualR3ShellProjFamily (K_max := K_max) k f‖ ≤ ‖f‖ := by
  exact (actualR3ShellProjectorData (K_max := K_max)).proj_contraction k f

/-- The actual Euclidean low-cutoff projector is also contractive on `L²(R³)^3`. -/
theorem actualR3LowCutoffComplex_contraction
    (Ncut : ℕ) (f : L2VecR3) :
    ‖actualR3LowCutoffComplex Ncut f‖ ≤ ‖f‖ := by
  have hmult :=
    lpCutoffMultiplier_norm_le (lowCutoffMultiplierLp Ncut) f
  have hcutoff : ‖lowCutoffMultiplierLp Ncut‖ ≤ 1 :=
    lowCutoffMultiplierLp_norm_le_one Ncut
  calc
    ‖actualR3LowCutoffComplex Ncut f‖
        = ‖lpCutoffMultiplier (lowCutoffMultiplierLp Ncut) f‖ := by
            rfl
    _ ≤ ‖lowCutoffMultiplierLp Ncut‖ * ‖f‖ := hmult
    _ ≤ 1 * ‖f‖ := by
      gcongr
    _ = ‖f‖ := by simp

end NSR3ProjectorContraction
