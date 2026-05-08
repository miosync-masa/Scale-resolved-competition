import NSBarrier.NSGalerkinCoeffODEProductRuleProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory
open NSTorusShellActual
open NSGalerkinCoeffODEProductRuleProof

namespace NSGalerkinIntegrabilityTheorems

-- ============================================================
-- [ODE] Interval integrability from continuous coefficients
--
-- PContOfCoeffs and DContOfCoeffs are finite sums of products
-- of continuous functions. If each coeff(·, κ) and nonlin(·, κ)
-- is continuous, the shellwise P and D are continuous, hence
-- interval integrable.
-- ============================================================

/-- [ODE] If each coefficient is continuous and each nonlinear term
is continuous, then the shellwise production is interval integrable. -/
theorem PCont_intervalIntegrable_of_continuous_coeff
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellOf : Mode → Fin K_max)
    (weight : Mode → ℝ)
    (coeff : ℝ → Mode → ℝ)
    (nonlin : ℝ → Mode → ℝ)
    (hcoeff_cont : ∀ κ : Mode, Continuous (fun t => coeff t κ))
    (hnonlin_cont : ∀ κ : Mode, Continuous (fun t => nonlin t κ))
    (a b : ℝ) (k : Fin K_max) :
    IntervalIntegrable
      (fun t => PContOfCoeffs modes shellOf weight coeff nonlin t k)
      volume a b := by
  unfold PContOfCoeffs
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_finset_sum
  intro κ _hκ
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact continuousOn_const
      · exact continuousOn_const
    · exact (hcoeff_cont κ).continuousOn
  · exact (hnonlin_cont κ).continuousOn

/-- [ODE] If each coefficient is continuous, then the shellwise
dissipation is interval integrable. -/
theorem DCont_intervalIntegrable_of_continuous_coeff
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellOf : Mode → Fin K_max)
    (weight : Mode → ℝ)
    (coeff : ℝ → Mode → ℝ)
    (damp : Mode → ℝ)
    (hcoeff_cont : ∀ κ : Mode, Continuous (fun t => coeff t κ))
    (a b : ℝ) (k : Fin K_max) :
    IntervalIntegrable
      (fun t => DContOfCoeffs modes shellOf weight coeff damp t k)
      volume a b := by
  unfold DContOfCoeffs
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_finset_sum
  intro κ _hκ
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact continuousOn_const
    · exact continuousOn_const
  · exact ((hcoeff_cont κ).pow 2).continuousOn

/-- [ODE] Continuity of coeff follows from HasDerivAt
(differentiable implies continuous). -/
theorem continuous_coeff_of_hasDeriv
    (coeff : ℝ → Mode → ℝ)
    (coeffDeriv : ℝ → Mode → ℝ)
    (hcoeff_hasDeriv : ∀ κ : Mode, ∀ t : ℝ,
      HasDerivAt (fun s => coeff s κ) (coeffDeriv t κ) t) :
    ∀ κ : Mode, Continuous (fun t => coeff t κ) := by
  intro κ
  rw [continuous_iff_continuousAt]
  intro t
  exact (hcoeff_hasDeriv κ t).continuousAt

#check @PCont_intervalIntegrable_of_continuous_coeff
#check @DCont_intervalIntegrable_of_continuous_coeff
#check @continuous_coeff_of_hasDeriv

end NSGalerkinIntegrabilityTheorems
