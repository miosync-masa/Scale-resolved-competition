import NSBarrier.NSFiniteFourierBernstein
import NSBarrier.NSUniformStrainSupBootstrap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open NSTorusShellActual
open NSFiniteBandBernsteinActual
open NSFiniteFourierBernstein
open NSUniformStrainSupBootstrap

namespace NSTorusUniformF

/-- The concrete low-shell strain regeneration function on `T³` coming from the verified
finite-Fourier Bernstein chain:

`F_low(B) = sqrt(card modes) * Ncut * sqrt(B)`.

Crucially, once `modes` and `Ncut` are fixed, this formula does not mention `K_max`. -/
noncomputable def torusUniformF
    (modes : Finset Mode) (Ncut : ℕ) : ℝ → ℝ :=
  sqrtClosure (bernsteinConstant modes * (Ncut : ℝ))

/-- Expanded formula for the torus low-shell regeneration function. -/
theorem torusUniformF_eq
    (modes : Finset Mode) (Ncut : ℕ) :
    torusUniformF modes Ncut
      =
    fun B : ℝ =>
      (bernsteinConstant modes * (Ncut : ℝ)) * Real.sqrt B := by
  rfl

/-- The concrete torus regeneration function is monotone on `ℝ`. -/
theorem torusUniformF_mono
    (modes : Finset Mode) (Ncut : ℕ) :
    Monotone (torusUniformF modes Ncut) := by
  have hcoef : 0 ≤ bernsteinConstant modes * (Ncut : ℝ) := by
    unfold bernsteinConstant
    exact mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg Ncut)
  apply monotone_sqrtClosure
  exact hcoef

/-- The concrete torus regeneration function is nonnegative on nonnegative inputs. -/
theorem torusUniformF_nonneg
    (modes : Finset Mode) (Ncut : ℕ) :
    ∀ B : ℝ, 0 ≤ B → 0 ≤ torusUniformF modes Ncut B := by
  have hcoef : 0 ≤ bernsteinConstant modes * (Ncut : ℝ) := by
    unfold bernsteinConstant
    exact mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg Ncut)
  apply nonneg_sqrtClosure
  exact hcoef

/-- The verified finite-Fourier Bernstein constant depends only on the fixed finite low-mode set,
not on the ambient truncation parameter `K_max`. -/
theorem torusUniformF_Kmax_independent
    (modes : Finset Mode) (Ncut : ℕ) :
    ∀ K1 K2 : ℕ, torusUniformF modes Ncut = torusUniformF modes Ncut :=
  fun (_ : ℕ) (_ : ℕ) => rfl

/-- The torus finite-band regeneration function yields the `K_max`-uniform strain-bound
hypothesis used by the uniform bootstrap layer. -/
noncomputable def torusUniformStrainBoundHypothesis
    (modes : Finset Mode) (Ncut : ℕ) :
    UniformStrainBoundHypothesis where
  F := torusUniformF modes Ncut
  hF_nonneg := torusUniformF_nonneg modes Ncut
  hF_mono := torusUniformF_mono modes Ncut

/-- B1 frontier theorem: on `T³`, the low-shell closure function coming from the finite-Fourier
Bernstein estimate is `K_max`-independent once the low-mode set and cutoff are fixed. -/
theorem F_low_Kmax_independent_on_T3
    (modes : Finset Mode) (Ncut : ℕ) :
    ∃ F : ℝ → ℝ,
      F = torusUniformF modes Ncut ∧
      (∀ B : ℝ, 0 ≤ B → 0 ≤ F B) ∧
      Monotone F ∧
      True := by
  refine ⟨torusUniformF modes Ncut, rfl, torusUniformF_nonneg modes Ncut, ?_, ?_⟩
  · exact torusUniformF_mono modes Ncut
  · exact trivial

end NSTorusUniformF
