import NSBarrier.NSTorusShellActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual

namespace NSStrainOpVectorActual

noncomputable abbrev Vec3 := EuclideanSpace ℂ (Fin 3)
noncomputable abbrev Mat3 := Vec3 →L[ℂ] Vec3
noncomputable abbrev μT3 : MeasureTheory.Measure T3 :=
  (MeasureTheory.volume : MeasureTheory.Measure T3)
noncomputable abbrev L2VecT3 :=
  MeasureTheory.Lp Vec3 (2 : ℝ≥0∞) μT3

/-- Vector-valued actual shellwise strain-operator data on `T³`.

This is the honest codomain for 3D Navier–Stokes:
- `omega k : T³ → ℂ³`
- `Sop k x : ℂ³ →L[ℂ] ℂ³`
- `sigma k : T³ → ℂ` is the scalar amplitude proxy, intended to dominate
  the pointwise operator norm of `Sop k x`.
-/
structure ShellStrainOperatorVecData (K_max : ℕ) where
  sigma : Fin K_max → T3 → ℂ
  omega : Fin K_max → T3 → Vec3
  Sop : Fin K_max → T3 → Mat3

  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3
  omega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (omega k) (2 : ℝ≥0∞) μT3
  Z_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => (Sop k x) (omega k x)) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

  /-- Pointwise operator-amplitude control. -/
  op_bound :
    ∀ k : Fin K_max, ∀ x : T3, ‖Sop k x‖ ≤ ‖sigma k x‖

#check @ShellStrainOperatorVecData

/-- Pointwise actual strain-action inequality in vector form:
    ‖S(x)(ω_k(x))‖ ≤ ‖sigma_k(x) * ω_k(x)‖. -/
theorem pointwise_dom_of_operator_bound_vec
    {K_max : ℕ}
    (sad : ShellStrainOperatorVecData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖(sad.Sop k x) (sad.omega k x)‖ ≤ ‖(sad.sigma k x) • (sad.omega k x)‖ := by
  intro k
  refine Filter.Eventually.of_forall ?_
  intro x
  have h1 :
      ‖(sad.Sop k x) (sad.omega k x)‖ ≤ ‖sad.Sop k x‖ * ‖sad.omega k x‖ := by
    simpa using (sad.Sop k x).le_opNorm (sad.omega k x)
  have h2 :
      ‖sad.Sop k x‖ * ‖sad.omega k x‖ ≤ ‖sad.sigma k x‖ * ‖sad.omega k x‖ := by
    exact mul_le_mul_of_nonneg_right (sad.op_bound k x) (norm_nonneg _)
  have h3 :
      ‖(sad.sigma k x) • (sad.omega k x)‖ = ‖sad.sigma k x‖ * ‖sad.omega k x‖ := by
    simp [norm_smul]
  calc
    ‖(sad.Sop k x) (sad.omega k x)‖ ≤ ‖sad.Sop k x‖ * ‖sad.omega k x‖ := h1
    _ ≤ ‖sad.sigma k x‖ * ‖sad.omega k x‖ := h2
    _ = ‖(sad.sigma k x) • (sad.omega k x)‖ := h3.symm

/-- The associated shellwise stretching output field. -/
noncomputable def shellStretchField
    {K_max : ℕ}
    (sad : ShellStrainOperatorVecData K_max) :
    Fin K_max → T3 → Vec3 :=
  fun k x => (sad.Sop k x) (sad.omega k x)

#check @pointwise_dom_of_operator_bound_vec
#check @shellStretchField

end NSStrainOpVectorActual
