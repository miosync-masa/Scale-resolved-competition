import NSBarrier.NSL2MultiplierTorus
import NSBarrier.NSL2MultiplierActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSL2MultiplierTorus
open NSL2MultiplierActual
open NSFourier
open NSAnalyticA1Locality

namespace NSStrainTensorActual

-- ============================================================
-- SECTION 1: SCALAR REDUCTION DATA
-- ============================================================

/-- Actual shellwise scalar-reduction data on `T³`.

This packages the reduction
  ‖Z_k‖_{L²} ≤ ‖σ_k ω_k‖_{L²}
together with the multiplier control
  ‖σ_k‖_{L∞} ≤ strainSup.
The intended application is `σ_k(x) = ‖S(x)‖_op`. -/
structure ShellStrainScalarReductionData (K_max : ℕ) where
  sigma : Fin K_max → T3 → ℂ
  omega : Fin K_max → T3 → ℂ
  Z : Fin K_max → T3 → ℂ

  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3
  omega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (omega k) (2 : ℝ≥0∞) μT3
  Z_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (Z k) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

  /-- The actual strain-to-scalar reduction:
      `Z_k` is dominated in `L²` by the scalar multiplier datum `σ_k · ω_k`. -/
  dominated_norm :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (Z k) (Z_mem k)‖ ≤
        ‖MeasureTheory.MemLp.toLp
            (fun x => sigma k x * omega k x)
            (MeasureTheory.MemLp.mul' (r := 2) (omega_mem k) (sigma_mem k))‖

#check @ShellStrainScalarReductionData

-- ============================================================
-- SECTION 2: FROM SCALAR REDUCTION TO ACTUAL STRAIN ACTION
-- ============================================================

/-- The shellwise `L²` strain-action bound obtained from scalar reduction
    and the actual `L∞ × L² → L²` multiplier theorem on `T³`. -/
theorem action_le_of_scalar_reduction
    {K_max : ℕ}
    (srd : ShellStrainScalarReductionData K_max) :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (srd.Z k) (srd.Z_mem k)‖ ≤
        srd.strainSup * ‖MeasureTheory.MemLp.toLp (srd.omega k) (srd.omega_mem k)‖ := by
  intro k
  have hdom :
      ‖MeasureTheory.MemLp.toLp (srd.Z k) (srd.Z_mem k)‖ ≤
        ‖MeasureTheory.MemLp.toLp
            (fun x => srd.sigma k x * srd.omega k x)
            (MeasureTheory.MemLp.mul' (r := 2) (srd.omega_mem k) (srd.sigma_mem k))‖ :=
    srd.dominated_norm k
  have hmult :
      ‖MeasureTheory.MemLp.toLp
          (fun x => srd.sigma k x * srd.omega k x)
          (MeasureTheory.MemLp.mul' (r := 2) (srd.omega_mem k) (srd.sigma_mem k))‖
        ≤
      (MeasureTheory.eLpNorm (srd.sigma k) ⊤ μT3).toReal *
        ‖MeasureTheory.MemLp.toLp (srd.omega k) (srd.omega_mem k)‖ :=
    l2_scalar_multiplier_norm_le
      (srd.sigma k) (srd.omega k)
      (srd.sigma_mem k) (srd.omega_mem k)
  exact le_trans hdom <|
    le_trans hmult <|
      mul_le_mul_of_nonneg_right
        (srd.sigma_bound k)
        (norm_nonneg (MeasureTheory.MemLp.toLp (srd.omega k) (srd.omega_mem k)))

#check @action_le_of_scalar_reduction

/-- Convert scalar-reduction data into the actual shell strain-action data
    used by the existing actual torus multiplier pipeline. -/
noncomputable def toActualShellStrainActionData
    {K_max : ℕ}
    (srd : ShellStrainScalarReductionData K_max) :
    ActualShellStrainActionData K_max where
  omega := fun k => MeasureTheory.MemLp.toLp (srd.omega k) (srd.omega_mem k)
  Z := fun k => MeasureTheory.MemLp.toLp (srd.Z k) (srd.Z_mem k)
  strainSup := srd.strainSup
  strainSup_nonneg := srd.strainSup_nonneg
  action_le := action_le_of_scalar_reduction srd

#check @toActualShellStrainActionData

-- ============================================================
-- SECTION 3: BRIDGE TO ProductionFromStrainSup
-- ============================================================

/-- Therefore scalar strain reduction on `T³` yields the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_scalar_reduction
    {K_max : ℕ}
    (srd : ShellStrainScalarReductionData K_max) :
    ProductionFromStrainSup
      (localizedProduction (actualLocalizedData (toActualShellStrainActionData srd)))
      (actualStrainState (toActualShellStrainActionData srd)) := by
  exact
    productionFromStrainSup_of_actual_strain_action
      (toActualShellStrainActionData srd)

#check @productionFromStrainSup_of_scalar_reduction

end NSStrainTensorActual
