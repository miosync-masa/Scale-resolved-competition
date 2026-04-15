import NSBarrier.NSStrainTensorActual
import NSBarrier.NSL2MultiplierTorus
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSL2MultiplierTorus
open NSL2MultiplierActual
open NSStrainTensorActual
open NSFourier
open NSAnalyticA1Locality

namespace NSVorticityTransportActual

/-
  We keep the codomain abstract for now.
  The immediate goal is not to formalize the full Navier–Stokes PDE,
  but to package the actual torus-side data needed to instantiate

    Z_k = S ω_k

  inside the already-proved `NSL2MultiplierTorus` bridge.
-/

-- ============================================================
-- SECTION 1: ABSTRACT POINTWISE STRAIN ACTION ON T³
-- ============================================================

/-- Actual shellwise strain-action data on `T³`.

`omega k` is the shell vorticity component.
`Z k` is the actual shellwise stretching output.
`sigma k` is the scalar operator-amplitude proxy, intended to be `‖S(·)‖op`.

The key input is the pointwise domination
  ‖Z_k(x)‖ ≤ |sigma_k(x)| · |omega_k(x)|.
-/
structure ShellPointwiseStrainActionData (K_max : ℕ) where
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

  /-- Pointwise actual strain-action inequality. -/
  pointwise_dom :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖Z k x‖ ≤ ‖sigma k x * omega k x‖

#check @ShellPointwiseStrainActionData

-- ============================================================
-- SECTION 2: POINTWISE DOMINATION -> L² DOMINATION
-- ============================================================

/-- Package the pointwise strain-action domination as the scalar reduction datum
    needed by the previous bridge. -/
theorem dominated_norm_of_pointwise_dom
    {K_max : ℕ}
    (sad : ShellPointwiseStrainActionData K_max) :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (sad.Z k) (sad.Z_mem k)‖ ≤
        ‖MeasureTheory.MemLp.toLp
          (fun x => sad.sigma k x * sad.omega k x)
          (MeasureTheory.MemLp.mul' (r := 2) (sad.omega_mem k) (sad.sigma_mem k))‖ := by
  intro k
  let hσω : MeasureTheory.MemLp
      (fun x => sad.sigma k x * sad.omega k x) (2 : ℝ≥0∞) μT3 :=
    MeasureTheory.MemLp.mul' (r := 2) (sad.omega_mem k) (sad.sigma_mem k)
  rw [MeasureTheory.Lp.norm_toLp (f := sad.Z k) (hf := sad.Z_mem k),
      MeasureTheory.Lp.norm_toLp (f := fun x => sad.sigma k x * sad.omega k x) (hf := hσω)]
  exact ENNReal.toReal_mono
    (ne_of_lt hσω.eLpNorm_lt_top)
    (MeasureTheory.eLpNorm_mono_ae (sad.pointwise_dom k))

-- ============================================================
-- SECTION 3: BRIDGE TO THE ACTUAL MULTIPLIER CHAIN
-- ============================================================

/-- Convert actual pointwise strain-action data into the scalar reduction data
    used by `NSStrainTensorActual`. -/
noncomputable def toScalarReductionData
    {K_max : ℕ}
    (sad : ShellPointwiseStrainActionData K_max) :
    ShellStrainScalarReductionData K_max where
  sigma := sad.sigma
  omega := sad.omega
  Z := sad.Z
  sigma_mem := sad.sigma_mem
  omega_mem := sad.omega_mem
  Z_mem := sad.Z_mem
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  sigma_bound := sad.sigma_bound
  dominated_norm := dominated_norm_of_pointwise_dom sad

#check @toScalarReductionData

/-- Therefore actual pointwise strain action on `T³` yields the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_pointwise_strain_action
    {K_max : ℕ}
    (sad : ShellPointwiseStrainActionData K_max) :
    ProductionFromStrainSup
      (localizedProduction
        (actualLocalizedData
          (toActualShellStrainActionData
            (toScalarReductionData sad))))
      (actualStrainState
        (toActualShellStrainActionData
          (toScalarReductionData sad))) := by
  exact
    productionFromStrainSup_of_scalar_reduction
      (toScalarReductionData sad)

#check @productionFromStrainSup_of_pointwise_strain_action

end NSVorticityTransportActual
