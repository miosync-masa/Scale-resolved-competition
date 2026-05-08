import NSBarrier.NSR3LittlewoodPaley
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3BernsteinProof

open NSR3ShellActual
open NSR3LittlewoodPaley

/-- The dyadic cutoff radius attached to shell cutoff `Ncut`. -/
noncomputable def cutoffRadius (Ncut : ℕ) : ℝ :=
  (2 : ℝ) ^ Ncut

/-- The Euclidean Bernstein constant coming from the volume of the low cutoff
ball `|ξ| ≤ 2^Ncut` in dimension `3`. -/
noncomputable def r3BernsteinConstant (Ncut : ℕ) : ℝ :=
  Real.sqrt (cutoffRadius Ncut ^ 3 * (Real.pi * 4 / 3))

theorem lowFrequencyCutoff_eq_closedBall (Ncut : ℕ) :
    lowFrequencyCutoff Ncut = Metric.closedBall (0 : Frequency) (cutoffRadius Ncut) := by
  ext ξ
  simp [lowFrequencyCutoff, lowBall, cutoffRadius, Metric.mem_closedBall, dist_zero_right]

theorem lowFrequencyCutoff_measure_eq (Ncut : ℕ) :
    μR3 (lowFrequencyCutoff Ncut)
      =
    ENNReal.ofReal (cutoffRadius Ncut) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [lowFrequencyCutoff_eq_closedBall, EuclideanSpace.volume_closedBall_fin_three]

theorem lowFrequencyCutoff_measure_toReal (Ncut : ℕ) :
    (μR3 (lowFrequencyCutoff Ncut)).toReal
      =
    cutoffRadius Ncut ^ 3 * (Real.pi * 4 / 3) := by
  have hcutoff : 0 ≤ cutoffRadius Ncut := by
    unfold cutoffRadius
    positivity
  have hgeom : 0 ≤ Real.pi * 4 / 3 := by positivity
  simpa [hcutoff, hgeom, Real.rpow_natCast] using
    congrArg ENNReal.toReal (lowFrequencyCutoff_measure_eq Ncut)

theorem lowFrequencyCutoff_measure_lt_top (Ncut : ℕ) :
    μR3 (lowFrequencyCutoff Ncut) < ∞ := by
  rw [lowFrequencyCutoff_measure_eq]
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  · exact ENNReal.ofReal_lt_top

theorem r3BernsteinConstant_nonneg (Ncut : ℕ) :
    0 ≤ r3BernsteinConstant Ncut := by
  unfold r3BernsteinConstant
  exact Real.sqrt_nonneg _

theorem lowFrequencyCutoff_measure_half_toReal (Ncut : ℕ) :
    ((μR3 (lowFrequencyCutoff Ncut)) ^ (1 / (2 : ℝ))).toReal
      =
    r3BernsteinConstant Ncut := by
  simpa [r3BernsteinConstant, Real.sqrt_eq_rpow, Real.rpow_natCast] using
    (by rw [← ENNReal.toReal_rpow, lowFrequencyCutoff_measure_toReal] :
      ((μR3 (lowFrequencyCutoff Ncut)) ^ (1 / (2 : ℝ))).toReal
        =
      (cutoffRadius Ncut ^ 3 * (Real.pi * 4 / 3)) ^ (1 / (2 : ℝ)))

/-- Analytic data for the Euclidean finite-band Bernstein inequality.

Interpretation:
- `coeffAbs n ξ` is the nonnegative frequency-side coefficient density
  controlling the local strain amplitude at time `n`;
- all coefficients are supported in the dyadic low ball `|ξ| ≤ 2^Ncut`;
- their `L²` norm is controlled by the chosen local H¹-type quantity.

Then finite-measure Hölder on the cutoff ball yields the Euclidean Bernstein
bound `L¹ ≤ |B_{2^Ncut}|^{1/2} L²`. -/
structure ActualR3BernsteinData where
  Ncut : ℕ
  localStrainAmp : ℕ → ℝ
  localH1Energy : ℕ → ℝ
  coeffAbs : ℕ → Frequency → ℝ
  hlocalStrain_nonneg : ∀ n : ℕ, 0 ≤ localStrainAmp n
  hlocalH1_nonneg : ∀ n : ℕ, 0 ≤ localH1Energy n
  hcoeff_nonneg : ∀ n : ℕ, ∀ ξ : Frequency, 0 ≤ coeffAbs n ξ
  hlocalStrain_l1 :
    ∀ n : ℕ,
      localStrainAmp n
        ≤
      (eLpNorm (coeffAbs n) (1 : ℝ≥0∞) μR3).toReal
  hcoeff_mem2 :
    ∀ n : ℕ, MemLp (coeffAbs n) (2 : ℝ≥0∞) μR3
  hcoeff_support :
    ∀ n : ℕ, Function.support (coeffAbs n) ⊆ lowFrequencyCutoff Ncut
  hcoeff_l2_to_localH1 :
    ∀ n : ℕ,
      (eLpNorm (coeffAbs n) (2 : ℝ≥0∞) μR3).toReal ≤ localH1Energy n

theorem r3_coeffLpOne_le_bernsteinConstant_mul_coeffLpTwo
    (ns : ActualR3BernsteinData) :
    ∀ n : ℕ,
      (eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μR3).toReal
        ≤
      r3BernsteinConstant ns.Ncut
        * (eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3).toReal := by
  intro n
  let s : Set Frequency := lowFrequencyCutoff ns.Ncut
  let μs : Measure Frequency := μR3.restrict s
  have hμs_fin : μR3 s ≠ ∞ := (lowFrequencyCutoff_measure_lt_top ns.Ncut).ne
  haveI : IsFiniteMeasure μs := MeasureTheory.isFiniteMeasure_restrict.2 hμs_fin
  have hmem2_restrict : MemLp (ns.coeffAbs n) (2 : ℝ≥0∞) μs :=
    (ns.hcoeff_mem2 n).restrict s
  have hrestrict_one :
      eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μs
        =
      eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μR3 := by
    exact eLpNorm_restrict_eq_of_support_subset (μ := μR3) (p := (1 : ℝ≥0∞))
      (ns.hcoeff_support n)
  have hrestrict_two :
      eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs
        =
      eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3 := by
    exact eLpNorm_restrict_eq_of_support_subset (μ := μR3) (p := (2 : ℝ≥0∞))
      (ns.hcoeff_support n)
  have hone_mem2 : MemLp (fun _ : Frequency => (1 : ℝ)) (ENNReal.ofReal 2) μs := by
    simpa using MeasureTheory.memLp_const (μ := μs) (p := (2 : ℝ≥0∞)) (1 : ℝ)
  have hholder :
      ∫ ξ, (1 : ℝ) * ns.coeffAbs n ξ ∂μs
        ≤
      (∫ ξ, (1 : ℝ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ))
        * (∫ ξ, (ns.coeffAbs n ξ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ)) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μs) hpq
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun ξ => ns.hcoeff_nonneg n ξ)
      hone_mem2 (show MemLp (ns.coeffAbs n) (ENNReal.ofReal 2) μs by
        simpa using hmem2_restrict)
  have hholder_abs :
      ∫ ξ, |ns.coeffAbs n ξ| ∂μs
        ≤
      (∫ ξ, (1 : ℝ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ))
        * (∫ ξ, (ns.coeffAbs n ξ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ)) := by
    have habs :
        ∫ ξ, |ns.coeffAbs n ξ| ∂μs = ∫ ξ, ns.coeffAbs n ξ ∂μs := by
      refine integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun ξ => ns.hcoeff_nonneg n ξ] with ξ hξ
      rw [abs_of_nonneg hξ]
    rw [habs]
    simpa using hholder
  have hholder_lp :
      MeasureTheory.lpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μs
        ≤
      MeasureTheory.lpNorm (fun _ : Frequency => (1 : ℝ)) (2 : ℝ≥0∞) μs
        * MeasureTheory.lpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs := by
    have hleft :
        ∫ ξ, (1 : ℝ) * ns.coeffAbs n ξ ∂μs
          =
        MeasureTheory.lpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μs := by
      rw [MeasureTheory.lpNorm_one_eq_integral_norm hmem2_restrict.1]
      refine integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun ξ => ns.hcoeff_nonneg n ξ] with ξ hξ
      rw [Real.norm_of_nonneg hξ]
      ring
    have hright_const :
        (∫ ξ, (1 : ℝ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ))
          =
        MeasureTheory.lpNorm (fun _ : Frequency => (1 : ℝ)) (2 : ℝ≥0∞) μs := by
      rw [MeasureTheory.lpNorm_const' (μ := μs) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) (1 : ℝ)]
      norm_num
    have hright_coeff :
        (∫ ξ, (ns.coeffAbs n ξ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ))
          =
        MeasureTheory.lpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs := by
      symm
      rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := μs) (p := (2 : ℝ≥0∞)) (f := ns.coeffAbs n) (by norm_num) (by norm_num)
        hmem2_restrict.1]
      have habs_sq :
          ∫ ξ, ‖ns.coeffAbs n ξ‖ ^ (2 : ℝ) ∂μs
            =
          ∫ ξ, (ns.coeffAbs n ξ) ^ (2 : ℝ) ∂μs := by
        refine integral_congr_ae ?_
        filter_upwards [Filter.Eventually.of_forall fun ξ => ns.hcoeff_nonneg n ξ] with ξ hξ
        rw [Real.norm_of_nonneg hξ]
      have hpow :
          (∫ x, ‖ns.coeffAbs n x‖ ^ ENNReal.toReal 2 ∂μs) ^ (ENNReal.toReal 2)⁻¹
            =
          (∫ ξ, ‖ns.coeffAbs n ξ‖ ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ)) := by
        norm_num
      rw [hpow, habs_sq]
    calc
      MeasureTheory.lpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μs
        = ∫ ξ, (1 : ℝ) * ns.coeffAbs n ξ ∂μs := by rw [← hleft]
      _ = ∫ ξ, |ns.coeffAbs n ξ| ∂μs := by
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall fun ξ => ns.hcoeff_nonneg n ξ] with ξ hξ
          rw [abs_of_nonneg hξ]
          ring
      _ ≤ (∫ ξ, (1 : ℝ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ))
            * (∫ ξ, (ns.coeffAbs n ξ) ^ (2 : ℝ) ∂μs) ^ (1 / (2 : ℝ)) := hholder_abs
      _ = MeasureTheory.lpNorm (fun _ : Frequency => (1 : ℝ)) (2 : ℝ≥0∞) μs
            * MeasureTheory.lpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs := by
          rw [hright_const, hright_coeff]
  have hμfactor :
      MeasureTheory.lpNorm (fun _ : Frequency => (1 : ℝ)) (2 : ℝ≥0∞) μs
        =
      r3BernsteinConstant ns.Ncut := by
    rw [MeasureTheory.lpNorm_const' (μ := μs) (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) (1 : ℝ)]
    have hμpow :
        (μR3 (lowFrequencyCutoff ns.Ncut)).toReal ^ (1 / (2 : ℝ))
          =
        r3BernsteinConstant ns.Ncut := by
      simpa [ENNReal.toReal_rpow] using lowFrequencyCutoff_measure_half_toReal ns.Ncut
    simpa [μs, s, Measure.real] using hμpow
  calc
    (eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μR3).toReal
      =
    MeasureTheory.lpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μs := by
        rw [← hrestrict_one, MeasureTheory.toReal_eLpNorm hmem2_restrict.1]
    _ ≤ MeasureTheory.lpNorm (fun _ : Frequency => (1 : ℝ)) (2 : ℝ≥0∞) μs
          * MeasureTheory.lpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs :=
        hholder_lp
    _ = r3BernsteinConstant ns.Ncut
          * MeasureTheory.lpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μs := by
        rw [hμfactor]
    _ = r3BernsteinConstant ns.Ncut
          * (eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3).toReal := by
        rw [← hrestrict_two, ← MeasureTheory.toReal_eLpNorm hmem2_restrict.1]

/-- The actual Euclidean finite-band Bernstein inequality on `R³`. -/
theorem r3_localStrainAmp_le_bernsteinConstant_mul_localH1Energy
    (ns : ActualR3BernsteinData) :
    ∀ n : ℕ,
      ns.localStrainAmp n
        ≤
      r3BernsteinConstant ns.Ncut * ns.localH1Energy n := by
  intro n
  have hcoeff :
      (eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μR3).toReal
        ≤
      r3BernsteinConstant ns.Ncut
        * (eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3).toReal :=
    r3_coeffLpOne_le_bernsteinConstant_mul_coeffLpTwo ns n
  have hmult :
      r3BernsteinConstant ns.Ncut
        * (eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3).toReal
          ≤
      r3BernsteinConstant ns.Ncut * ns.localH1Energy n := by
    exact mul_le_mul_of_nonneg_left
      (ns.hcoeff_l2_to_localH1 n) (r3BernsteinConstant_nonneg ns.Ncut)
  calc
    ns.localStrainAmp n
      ≤
    (eLpNorm (ns.coeffAbs n) (1 : ℝ≥0∞) μR3).toReal :=
      ns.hlocalStrain_l1 n
    _ ≤ r3BernsteinConstant ns.Ncut
          * (eLpNorm (ns.coeffAbs n) (2 : ℝ≥0∞) μR3).toReal :=
      hcoeff
    _ ≤ r3BernsteinConstant ns.Ncut * ns.localH1Energy n :=
      hmult

end NSR3BernsteinProof
