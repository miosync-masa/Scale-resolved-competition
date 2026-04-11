import NSBarrier.NSTorusShellActual
import NSBarrier.NSL2MultiplierActual
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSL2MultiplierActual
open NSFourier
open NSAnalyticA1Locality

namespace NSL2MultiplierTorus

noncomputable abbrev μT3 : MeasureTheory.Measure T3 :=
  (MeasureTheory.volume : MeasureTheory.Measure T3)

-- ============================================================
-- SECTION 1: ACTUAL SCALAR MULTIPLIER ON T³
-- ============================================================

/-- Actual scalar multiplier estimate on `T³`:
    ‖σ f‖_{L²} ≤ ‖σ‖_{L∞} ‖f‖_{L²}. -/
theorem l2_scalar_multiplier_eLpNorm_le
    (σ f : T3 → ℂ)
    (hf : AEStronglyMeasurable f μT3) :
    MeasureTheory.eLpNorm (fun x => σ x * f x) (2 : ℝ≥0∞) μT3
      ≤
    MeasureTheory.eLpNorm σ ⊤ μT3
      * MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μT3 := by
  have h_mul :
      ∀ᵐ x ∂ μT3,
        ‖(σ x) * (f x)‖₊ ≤
          (1 : NNReal) * ‖σ x‖₊ * ‖f x‖₊ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [nnnorm_mul, mul_comm]
  simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using
    (MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm
      (p := (2 : ℝ≥0∞))
      (f := σ)
      (g := f)
      (μ := μT3)
      hf
      (fun a b => a * b)
      (1 : NNReal)
      h_mul)

/-- The same scalar multiplier estimate, but on actual `Lp` elements. -/
theorem l2_scalar_multiplier_norm_le
    (σ f : T3 → ℂ)
    (hσ : MeasureTheory.MemLp σ ⊤ μT3)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) μT3) :
    ‖MeasureTheory.MemLp.toLp
        (fun x => σ x * f x)
        (MeasureTheory.MemLp.mul' (r := 2) hf hσ)‖
      ≤
    (MeasureTheory.eLpNorm σ ⊤ μT3).toReal
      * ‖MeasureTheory.MemLp.toLp f hf‖ := by
  let hσf : MeasureTheory.MemLp (fun x => σ x * f x) (2 : ℝ≥0∞) μT3 :=
    MeasureTheory.MemLp.mul' (r := 2) hf hσ
  rw [MeasureTheory.Lp.norm_toLp (f := fun x => σ x * f x) (hf := hσf),
      MeasureTheory.Lp.norm_toLp (f := f) (hf := hf)]
  have hmain :
      MeasureTheory.eLpNorm (fun x => σ x * f x) (2 : ℝ≥0∞) μT3
        ≤
      MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μT3 :=
    l2_scalar_multiplier_eLpNorm_le σ f hf.aestronglyMeasurable
  have hleft_ne :
      MeasureTheory.eLpNorm (fun x => σ x * f x) (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ne_of_lt hσf.eLpNorm_lt_top
  have hσ_ne : MeasureTheory.eLpNorm σ ⊤ μT3 ≠ ⊤ := by
    exact ne_of_lt hσ.eLpNorm_lt_top
  have hf_ne : MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ne_of_lt hf.eLpNorm_lt_top
  have hprod_ne :
      MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hσ_ne hf_ne
  have hmain' :
      (MeasureTheory.eLpNorm (fun x => σ x * f x) (2 : ℝ≥0∞) μT3).toReal
        ≤
      (MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μT3).toReal := by
    exact (ENNReal.toReal_le_toReal hleft_ne hprod_ne).2 hmain
  simpa [ENNReal.toReal_mul, hσ_ne, hf_ne] using hmain'

#check @l2_scalar_multiplier_eLpNorm_le
#check @l2_scalar_multiplier_norm_le

-- ============================================================
-- SECTION 2: PACKAGE THE MULTIPLIER INPUT SHELLWISE
-- ============================================================

/-- Shellwise actual scalar-multiplier data on `T³`. -/
structure ScalarMultiplierTorusData (K_max : ℕ) where
  sigma : Fin K_max → T3 → ℂ
  omega : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3
  omega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (omega k) (2 : ℝ≥0∞) μT3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

#check @ScalarMultiplierTorusData

/-- Convert shellwise scalar-multiplier data into actual shell strain-action data
    for the already-built actual projector chain. -/
noncomputable def toActualShellStrainActionData {K_max : ℕ}
    (smd : ScalarMultiplierTorusData K_max) :
    ActualShellStrainActionData K_max where
  omega := fun k => MeasureTheory.MemLp.toLp (smd.omega k) (smd.omega_mem k)
  Z := fun k =>
    MeasureTheory.MemLp.toLp
      (fun x => smd.sigma k x * smd.omega k x)
      (MeasureTheory.MemLp.mul' (r := 2) (smd.omega_mem k) (smd.sigma_mem k))
  strainSup := smd.strainSup
  strainSup_nonneg := smd.strainSup_nonneg
  action_le := by
    intro k
    have hk :=
      l2_scalar_multiplier_norm_le
        (smd.sigma k) (smd.omega k)
        (smd.sigma_mem k) (smd.omega_mem k)
    exact le_trans hk
      (mul_le_mul_of_nonneg_right (smd.sigma_bound k)
        (norm_nonneg (MeasureTheory.MemLp.toLp (smd.omega k) (smd.omega_mem k))))

/-- Therefore the actual torus multiplier input yields the abstract
    `ProductionFromStrainSup` needed by the barrier pipeline. -/
theorem productionFromStrainSup_of_scalar_multiplier_torus
    {K_max : ℕ}
    (smd : ScalarMultiplierTorusData K_max) :
    ProductionFromStrainSup
      (localizedProduction (actualLocalizedData (toActualShellStrainActionData smd)))
      (actualStrainState (toActualShellStrainActionData smd)) := by
  exact productionFromStrainSup_of_actual_strain_action
    (toActualShellStrainActionData smd)

#check @toActualShellStrainActionData
#check @productionFromStrainSup_of_scalar_multiplier_torus

end NSL2MultiplierTorus
