import NSBarrier.NSVorticityTransportActual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSL2MultiplierTorus
open NSL2MultiplierActual
open NSStrainTensorActual
open NSVorticityTransportActual
open NSFourier
open NSAnalyticA1Locality

namespace NSStrainOpActual

-- ============================================================
-- SECTION 1: ACTUAL OPERATOR-VALUED STRAIN DATA
-- ============================================================

/-- Actual shellwise strain-operator data on `T³`.

`Sop k x` is the pointwise operator acting on the shell field `omega k x`.
`sigma k x` is a scalar amplitude proxy, intended to dominate `‖Sop k x‖`.
The output field is `x ↦ Sop k x (omega k x)`.
-/
structure ShellStrainOperatorData (K_max : ℕ) where
  sigma : Fin K_max → T3 → ℂ
  omega : Fin K_max → T3 → ℂ
  Sop : Fin K_max → T3 → (ℂ →L[ℂ] ℂ)

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

#check @ShellStrainOperatorData

-- ============================================================
-- SECTION 2: POINTWISE DOMINATION
-- ============================================================

/-- Pointwise actual strain-action inequality derived from the operator norm bound:
    ‖S(x)(ω_k(x))‖ ≤ ‖sigma_k(x) * omega_k(x)‖. -/
theorem pointwise_dom_of_operator_bound
    {K_max : ℕ}
    (sad : ShellStrainOperatorData K_max) :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖(sad.Sop k x) (sad.omega k x)‖ ≤ ‖sad.sigma k x * sad.omega k x‖ := by
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
      ‖sad.sigma k x‖ * ‖sad.omega k x‖ = ‖sad.sigma k x * sad.omega k x‖ := by
    simp
  exact le_trans h1 (h3 ▸ h2)

#check @pointwise_dom_of_operator_bound

-- ============================================================
-- SECTION 3: BRIDGE TO THE POINTWISE STRAIN-ACTION CHAIN
-- ============================================================

/-- Convert actual operator-valued strain data into the pointwise scalar-dominated
    strain-action data used by `NSVorticityTransportActual`. -/
noncomputable def toShellPointwiseStrainActionData
    {K_max : ℕ}
    (sad : ShellStrainOperatorData K_max) :
    ShellPointwiseStrainActionData K_max where
  sigma := sad.sigma
  omega := sad.omega
  Z := fun k x => (sad.Sop k x) (sad.omega k x)
  sigma_mem := sad.sigma_mem
  omega_mem := sad.omega_mem
  Z_mem := sad.Z_mem
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  sigma_bound := sad.sigma_bound
  pointwise_dom := pointwise_dom_of_operator_bound sad

#check @toShellPointwiseStrainActionData

-- ============================================================
-- SECTION 4: FINAL BRIDGE TO ProductionFromStrainSup
-- ============================================================

/-- Therefore actual pointwise operator-valued strain action on `T³`
    yields the abstract `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_strain_operator
    {K_max : ℕ}
    (sad : ShellStrainOperatorData K_max) :
    ProductionFromStrainSup
      (localizedProduction
        (actualLocalizedData
          (toActualShellStrainActionData
            (toScalarReductionData
              (toShellPointwiseStrainActionData sad)))))
      (actualStrainState
        (toActualShellStrainActionData
          (toScalarReductionData
            (toShellPointwiseStrainActionData sad)))) := by
  exact
    productionFromStrainSup_of_pointwise_strain_action
      (toShellPointwiseStrainActionData sad)

#check @productionFromStrainSup_of_strain_operator

end NSStrainOpActual
