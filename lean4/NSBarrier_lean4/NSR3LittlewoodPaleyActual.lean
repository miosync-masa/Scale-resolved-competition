import NSBarrier.NSR3LittlewoodPaley
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell

namespace NSR3LittlewoodPaleyActual

open NSR3ShellActual
open NSR3LittlewoodPaley

noncomputable abbrev Vec3 := EuclideanSpace ℂ (Fin 3)
noncomputable abbrev L2VecR3 :=
  MeasureTheory.Lp Vec3 (2 : ℝ≥0∞) μR3
noncomputable abbrev LInfScalarR3 :=
  MeasureTheory.Lp ℂ ⊤ μR3

noncomputable instance : InnerProductSpace ℝ L2VecR3 :=
  InnerProductSpace.rclikeToReal ℂ L2VecR3

instance : LinearMap.CompatibleSMul L2VecR3 L2VecR3 ℝ ℂ where
  map_smul fₗ r x := fₗ.map_smul (r : ℂ) x

/-- The canonical shell multiplier on Euclidean frequency space. -/
noncomputable def shellMultiplier {K_max : ℕ} (k : Fin K_max) : Frequency → ℂ :=
  Set.indicator (shellRegion k) (fun _ => (1 : ℂ))

/-- The canonical low-cutoff multiplier on Euclidean frequency space. -/
noncomputable def lowCutoffMultiplier (Ncut : ℕ) : Frequency → ℂ :=
  Set.indicator (lowFrequencyCutoff Ncut) (fun _ => (1 : ℂ))

theorem measurableSet_shellRegion {K_max : ℕ} (k : Fin K_max) :
    MeasurableSet (shellRegion k) := by
  have hlower :
      IsClosed {ξ : Frequency | (2 : ℝ) ^ k.val ≤ ‖ξ‖} :=
    isClosed_le continuous_const continuous_norm
  have hupper :
      IsOpen {ξ : Frequency | ‖ξ‖ < (2 : ℝ) ^ (k.val + 1)} :=
    isOpen_lt continuous_norm continuous_const
  change MeasurableSet {ξ : Frequency | (2 : ℝ) ^ k.val ≤ ‖ξ‖ ∧ ‖ξ‖ < (2 : ℝ) ^ (k.val + 1)}
  exact hlower.measurableSet.inter hupper.measurableSet

theorem measurableSet_lowFrequencyCutoff (Ncut : ℕ) :
    MeasurableSet (lowFrequencyCutoff Ncut) := by
  simpa [lowFrequencyCutoff, lowBall] using
    (isClosed_le continuous_norm continuous_const).measurableSet

theorem shellMultiplier_memLp {K_max : ℕ} (k : Fin K_max) :
    MemLp (shellMultiplier k) ⊤ μR3 := by
  simpa [shellMultiplier] using
    (MeasureTheory.memLp_top_const (μ := μR3) (1 : ℂ)).indicator
      (measurableSet_shellRegion k)

theorem lowCutoffMultiplier_memLp (Ncut : ℕ) :
    MemLp (lowCutoffMultiplier Ncut) ⊤ μR3 := by
  simpa [lowCutoffMultiplier] using
    (MeasureTheory.memLp_top_const (μ := μR3) (1 : ℂ)).indicator
      (measurableSet_lowFrequencyCutoff Ncut)

noncomputable def shellMultiplierLp {K_max : ℕ} (k : Fin K_max) : LInfScalarR3 :=
  MemLp.toLp (shellMultiplier k) (shellMultiplier_memLp k)

noncomputable def lowCutoffMultiplierLp (Ncut : ℕ) : LInfScalarR3 :=
  MemLp.toLp (lowCutoffMultiplier Ncut) (lowCutoffMultiplier_memLp Ncut)

theorem shellMultiplierLp_norm_le_one {K_max : ℕ} (k : Fin K_max) :
    ‖shellMultiplierLp k‖ ≤ 1 := by
  change ‖MemLp.toLp (shellMultiplier k) (shellMultiplier_memLp k)‖ ≤ 1
  rw [MeasureTheory.Lp.norm_toLp (f := shellMultiplier k) (hf := shellMultiplier_memLp k)]
  have hmain :
      MeasureTheory.eLpNormEssSup (shellMultiplier k) μR3 ≤ 1 := by
    simpa [shellMultiplier] using
      (MeasureTheory.eLpNormEssSup_indicator_const_le
        (μ := μR3) (s := shellRegion k) (c := (1 : ℂ)))
  have hleft :
      MeasureTheory.eLpNormEssSup (shellMultiplier k) μR3 ≠ ⊤ := by
    simpa [shellMultiplier, MeasureTheory.eLpNorm_exponent_top] using
      (ne_of_lt (shellMultiplier_memLp k).eLpNorm_lt_top)
  exact (ENNReal.toReal_le_toReal hleft ENNReal.one_ne_top).2 hmain

theorem lowCutoffMultiplierLp_norm_le_one (Ncut : ℕ) :
    ‖lowCutoffMultiplierLp Ncut‖ ≤ 1 := by
  change ‖MemLp.toLp (lowCutoffMultiplier Ncut) (lowCutoffMultiplier_memLp Ncut)‖ ≤ 1
  rw [MeasureTheory.Lp.norm_toLp
    (f := lowCutoffMultiplier Ncut) (hf := lowCutoffMultiplier_memLp Ncut)]
  have hmain :
      MeasureTheory.eLpNormEssSup (lowCutoffMultiplier Ncut) μR3 ≤ 1 := by
    simpa [lowCutoffMultiplier] using
      (MeasureTheory.eLpNormEssSup_indicator_const_le
        (μ := μR3) (s := lowFrequencyCutoff Ncut) (c := (1 : ℂ)))
  have hleft :
      MeasureTheory.eLpNormEssSup (lowCutoffMultiplier Ncut) μR3 ≠ ⊤ := by
    simpa [lowCutoffMultiplier, MeasureTheory.eLpNorm_exponent_top] using
      (ne_of_lt (lowCutoffMultiplier_memLp Ncut).eLpNorm_lt_top)
  exact (ENNReal.toReal_le_toReal hleft ENNReal.one_ne_top).2 hmain

/-- Multiplication by a bounded scalar frequency cutoff on `L²(R³)^3`. -/
noncomputable def lpCutoffMultiplier :
    LInfScalarR3 →L[ℂ] L2VecR3 →L[ℂ] L2VecR3 :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := Vec3)).holderL
    μR3 (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)

theorem lpCutoffMultiplier_norm_le (φ : LInfScalarR3) (f : L2VecR3) :
    ‖lpCutoffMultiplier φ f‖ ≤ ‖φ‖ * ‖f‖ := by
  simpa [lpCutoffMultiplier] using MeasureTheory.Lp.norm_smul_le φ f

/-- The concrete Euclidean shell projector obtained by cutting off the Fourier
side, interpreted directly as the ambient `L²(R³)` state space. -/
noncomputable def actualR3ShellProjComplex {K_max : ℕ} (k : Fin K_max) :
    L2VecR3 →L[ℂ] L2VecR3 :=
  lpCutoffMultiplier (shellMultiplierLp k)

/-- The concrete Euclidean low-cutoff operator obtained by cutting off the
frequency side to `|ξ| ≤ 2^Ncut`. -/
noncomputable def actualR3LowCutoffComplex (Ncut : ℕ) :
    L2VecR3 →L[ℂ] L2VecR3 :=
  lpCutoffMultiplier (lowCutoffMultiplierLp Ncut)

/-- The actual Euclidean shell projector family, viewed over `ℝ` so it can feed
the existing barrier chain. -/
noncomputable def actualR3ShellProjFamily {K_max : ℕ} (k : Fin K_max) :
    L2VecR3 →L[ℝ] L2VecR3 :=
  (actualR3ShellProjComplex k).restrictScalars ℝ

/-- The concrete Euclidean shell projectors packaged for the abstract barrier
interfaces. -/
noncomputable def actualR3ShellProjectorData {K_max : ℕ} :
    ShellProjectorData L2VecR3 K_max where
  Pk := fun k => (actualR3ShellProjFamily k).toLinearMap
  proj_contraction := by
    intro k z
    simpa [actualR3ShellProjFamily] using
      (by
        have hmult :=
          lpCutoffMultiplier_norm_le (shellMultiplierLp k) z
        have hcutoff : ‖shellMultiplierLp k‖ ≤ 1 :=
          shellMultiplierLp_norm_le_one k
        calc
          ‖actualR3ShellProjComplex k z‖
              = ‖lpCutoffMultiplier (shellMultiplierLp k) z‖ := by
                  rfl
          _ ≤ ‖shellMultiplierLp k‖ * ‖z‖ := hmult
          _ ≤ 1 * ‖z‖ := by
            gcongr
          _ = ‖z‖ := by simp)

/-- Actual Euclidean Littlewood-Paley data: the concrete projector family
plus the canonical dyadic shell and low-cutoff geometry. -/
structure ActualR3LittlewoodPaleyData (K_max : ℕ) where
  projData : ShellProjectorData L2VecR3 K_max
  shellSet : Fin K_max → Set Frequency
  lowCutoff : ℕ → Set Frequency

/-- The actual Euclidean shell projector family carries the canonical dyadic
shell geometry and low-frequency cutoffs. -/
noncomputable def actualR3LittlewoodPaleyData (K_max : ℕ) :
    ActualR3LittlewoodPaleyData K_max where
  projData := actualR3ShellProjectorData (K_max := K_max)
  shellSet := shellRegion
  lowCutoff := lowFrequencyCutoff

end NSR3LittlewoodPaleyActual
