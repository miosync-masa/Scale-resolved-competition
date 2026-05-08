import NSBarrier.NSR3FiniteBandSobolevBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace NSR3FiniteBandBernstein

open NSFiniteBandBernsteinActual
open NSR3BernsteinProof

/-- Re-export the dyadic Euclidean cutoff radius. -/
noncomputable abbrev cutoffRadius := NSR3BernsteinProof.cutoffRadius

/-- Re-export the theorem-backed Euclidean Bernstein constant. -/
noncomputable abbrev r3BernsteinConstant := NSR3BernsteinProof.r3BernsteinConstant

/-- The associated finite-band closure function on `R^3`. -/
noncomputable def r3FiniteBandClosure (Ncut : ℕ) : ℝ → ℝ :=
  sqrtClosure (r3BernsteinConstant Ncut)

/-- Expanded formula for the theorem-backed Euclidean finite-band closure
function. -/
theorem r3FiniteBandClosure_eq (Ncut : ℕ) :
    r3FiniteBandClosure Ncut
      =
    fun B : ℝ =>
      r3BernsteinConstant Ncut * Real.sqrt B := by
  rfl

theorem r3BernsteinConstant_nonneg (Ncut : ℕ) :
    0 ≤ r3BernsteinConstant Ncut :=
  NSR3BernsteinProof.r3BernsteinConstant_nonneg Ncut

theorem monotone_r3FiniteBandClosure (Ncut : ℕ) :
    Monotone (r3FiniteBandClosure Ncut) := by
  apply monotone_sqrtClosure
  exact r3BernsteinConstant_nonneg Ncut

theorem nonneg_r3FiniteBandClosure (Ncut : ℕ) :
    ∀ B : ℝ, 0 ≤ B → 0 ≤ r3FiniteBandClosure Ncut B := by
  apply nonneg_sqrtClosure
  exact r3BernsteinConstant_nonneg Ncut

/-- C3 theorem, now in theorem-backed form: the Euclidean `R^3` branch carries
the canonical square-root closure coming from the finite volume of the frequency
cutoff ball `|ξ| ≤ 2^Ncut`. -/
theorem R3_finite_band_bernstein (Ncut : ℕ) :
    ∃ F : ℝ → ℝ,
      F = r3FiniteBandClosure Ncut ∧
      (∀ B : ℝ, 0 ≤ B → 0 ≤ F B) ∧
      Monotone F := by
  refine ⟨r3FiniteBandClosure Ncut, rfl, ?_, ?_⟩
  · exact nonneg_r3FiniteBandClosure Ncut
  · exact monotone_r3FiniteBandClosure Ncut

end NSR3FiniteBandBernstein
