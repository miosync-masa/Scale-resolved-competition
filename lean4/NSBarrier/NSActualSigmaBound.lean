import NSBarrier.NSStrainOpVectorActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual

namespace NSActualSigmaBound

/-- Canonical scalar amplitude associated to the pointwise operator field:
    σ_k(x) := ‖Sop_k(x)‖, embedded into `ℂ`. -/
noncomputable def sigmaFromOpNorm {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3) :
    Fin K_max → T3 → ℂ :=
  fun k x => Complex.ofReal ‖Sop k x‖

@[simp] theorem norm_sigmaFromOpNorm
    {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3)
    (k : Fin K_max) (x : T3) :
    ‖sigmaFromOpNorm Sop k x‖ = ‖Sop k x‖ := by
  simp [sigmaFromOpNorm]

/-- Hence the pointwise operator norm is dominated by the canonical scalar amplitude. -/
theorem op_bound_of_sigmaFromOpNorm
    {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3) :
    ∀ k : Fin K_max, ∀ x : T3, ‖Sop k x‖ ≤ ‖sigmaFromOpNorm Sop k x‖ := by
  intro k x
  simp [sigmaFromOpNorm]

#check @sigmaFromOpNorm
#check @norm_sigmaFromOpNorm
#check @op_bound_of_sigmaFromOpNorm

-- ============================================================
-- SECTION 1: CORE DATA FOR σ = ‖Sop‖op
-- ============================================================

/-- Core data for supplying the `sigma`-side fields of
    `ShellStrainOperatorVecData` via the canonical choice `σ = ‖Sop‖op`.

What still has to come from actual Navier–Stokes fields is:
- `omega`
- `omega_mem`
- `Z_mem`
- the actual `L∞` bound on `σ = ‖Sop‖op`.
-/
structure ShellStrainOperatorSigmaCoreData (K_max : ℕ) where
  Sop : Fin K_max → T3 → Mat3

  omega : Fin K_max → T3 → Vec3
  omega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (omega k) (2 : ℝ≥0∞) μT3

  Z_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => (Sop k x) (omega k x)) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- The actual `L∞` control on `σ = ‖Sop‖op`. -/
  sigma_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (sigmaFromOpNorm Sop k) ⊤ μT3

  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigmaFromOpNorm Sop k) ⊤ μT3).toReal ≤ strainSup

#check @ShellStrainOperatorSigmaCoreData

-- ============================================================
-- SECTION 2: BRIDGE TO ShellStrainOperatorVecData
-- ============================================================

/-- Turn the core `σ = ‖Sop‖op` data into the actual vector-valued
    strain-operator package used downstream. -/
noncomputable def toShellStrainOperatorVecData
    {K_max : ℕ}
    (sad : ShellStrainOperatorSigmaCoreData K_max) :
    ShellStrainOperatorVecData K_max where
  sigma := sigmaFromOpNorm sad.Sop
  omega := sad.omega
  Sop := sad.Sop
  sigma_mem := sad.sigma_mem
  omega_mem := sad.omega_mem
  Z_mem := sad.Z_mem
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  sigma_bound := sad.sigma_bound
  op_bound := op_bound_of_sigmaFromOpNorm sad.Sop

#check @toShellStrainOperatorVecData

-- ============================================================
-- SECTION 3: SIMPLE CONSEQUENCES
-- ============================================================

/-- The packaged scalar amplitude is indeed the operator norm amplitude. -/
@[simp] theorem sigma_eq_sigmaFromOpNorm
    {K_max : ℕ}
    (sad : ShellStrainOperatorSigmaCoreData K_max)
    (k : Fin K_max) (x : T3) :
    (toShellStrainOperatorVecData sad).sigma k x = sigmaFromOpNorm sad.Sop k x := rfl

/-- The packaged operator field is the original operator field. -/
@[simp] theorem Sop_eq_original
    {K_max : ℕ}
    (sad : ShellStrainOperatorSigmaCoreData K_max)
    (k : Fin K_max) (x : T3) :
    (toShellStrainOperatorVecData sad).Sop k x = sad.Sop k x := rfl

/-- The packaged shell field is the original shell field. -/
@[simp] theorem omega_eq_original
    {K_max : ℕ}
    (sad : ShellStrainOperatorSigmaCoreData K_max)
    (k : Fin K_max) (x : T3) :
    (toShellStrainOperatorVecData sad).omega k x = sad.omega k x := rfl

#check @sigma_eq_sigmaFromOpNorm
#check @Sop_eq_original
#check @omega_eq_original

end NSActualSigmaBound
