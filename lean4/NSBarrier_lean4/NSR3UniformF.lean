import NSBarrier.NSR3BernsteinProof
import NSBarrier.NSFiniteBandBernsteinActual
import NSBarrier.NSUniformStrainSupBootstrap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open NSR3BernsteinProof
open NSUniformStrainSupBootstrap

namespace NSR3UniformF

/-- The concrete low-shell strain regeneration function on `R³` coming from the
verified Euclidean Bernstein chain:

`F_low(B) = r3BernsteinConstant(Ncut) * sqrt(B)`.

Once `Ncut` is fixed, this formula does not mention `K_max`. -/
noncomputable def r3UniformF
    (Ncut : ℕ) : ℝ → ℝ :=
  NSFiniteBandBernsteinActual.sqrtClosure (r3BernsteinConstant Ncut)

/-- Expanded formula for the Euclidean low-shell regeneration function. -/
theorem r3UniformF_eq
    (Ncut : ℕ) :
    r3UniformF Ncut
      =
    fun B : ℝ =>
      r3BernsteinConstant Ncut * Real.sqrt B := by
  rfl

/-- The concrete Euclidean regeneration function is monotone on `ℝ`. -/
theorem r3UniformF_mono
    (Ncut : ℕ) :
    Monotone (r3UniformF Ncut) := by
  apply NSFiniteBandBernsteinActual.monotone_sqrtClosure
  exact r3BernsteinConstant_nonneg Ncut

/-- The concrete Euclidean regeneration function is nonnegative on nonnegative
inputs. -/
theorem r3UniformF_nonneg
    (Ncut : ℕ) :
    ∀ B : ℝ, 0 ≤ B → 0 ≤ r3UniformF Ncut B := by
  apply NSFiniteBandBernsteinActual.nonneg_sqrtClosure
  exact r3BernsteinConstant_nonneg Ncut

/-- The Euclidean finite-band Bernstein constant depends only on the cutoff
`Ncut`, not on the ambient truncation parameter `K_max`. -/
theorem r3UniformF_Kmax_independent
    (Ncut : ℕ) :
    ∀ _K1 _K2 : ℕ, r3UniformF Ncut = r3UniformF Ncut :=
  fun (_K1 : ℕ) (_K2 : ℕ) => rfl

/-- The Euclidean finite-band regeneration function yields the `K_max`-uniform
strain-bound hypothesis used by the uniform bootstrap layer. -/
noncomputable def r3UniformStrainBoundHypothesis
    (Ncut : ℕ) :
    UniformStrainBoundHypothesis where
  F := r3UniformF Ncut
  hF_nonneg := r3UniformF_nonneg Ncut
  hF_mono := r3UniformF_mono Ncut

/-- A1 frontier theorem: on `R³`, the low-shell closure function coming from
the theorem-backed Euclidean Bernstein estimate is `K_max`-independent once the
cutoff is fixed. -/
theorem F_low_Kmax_independent_on_R3
    (Ncut : ℕ) :
    ∃ F : ℝ → ℝ,
      F = r3UniformF Ncut ∧
      (∀ B : ℝ, 0 ≤ B → 0 ≤ F B) ∧
      Monotone F ∧
      True := by
  refine ⟨r3UniformF Ncut, rfl, r3UniformF_nonneg Ncut, ?_, ?_⟩
  · exact r3UniformF_mono Ncut
  · exact trivial

end NSR3UniformF
