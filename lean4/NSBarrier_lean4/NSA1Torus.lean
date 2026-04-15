import NSBarrier.NSFourier
import NSBarrier.NSAnalyticA
import NSBarrier.NSTorusShell
import NSBarrier.NSAnalyticA1Pairing
import NSBarrier.NSAnalyticA1Locality
import NSBarrier.NSL2Multiplier
import NSBarrier.NSStrainAction
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open NSFourier
open NSAnalyticA
open NSTorusShell
open NSAnalyticA1Pairing
open NSAnalyticA1Locality
open NSL2Multiplier
open NSStrainAction
open scoped InnerProductSpace

/-!
# NSA1Torus

Final capstone file for the abstract A1 pipeline on the torus-facing side.

This file does not yet construct the actual shell projectors on `T^3`; instead it
packages the already-proved abstract chain

  projector contraction
  + multiplier/strain action
  + pairing bound
  -> LocalizedProjectedStretching
  -> GradientControlledByStrain
  -> ProductionFromStrainSup.

The intended eventual instantiation is `V = L²(T³)^3` with shell projectors coming
from Fourier-shell orthogonal projections.
-/

namespace NSA1Torus

/-- The 3-dimensional torus `(ℝ/ℤ)^3`. -/
abbrev T3 := NSTorusShell.T3

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- ============================================================
-- SECTION 1: A1 CORE BOUNDS
-- ============================================================

/-- A1 absolute shellwise production bound:
    `|P_k| ≤ strainSup · Ξ_k`. -/
theorem A1_localized_shell_bound_abs
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ∀ k : Fin K_max,
      |localizedProduction (localizedData sad) k|
        ≤ sad.strainSup * localizedVortSq (localizedData sad) k := by
  intro k
  simpa [localizedData, toMultiplierData] using
    (localized_shell_bound_abs (localizedData sad) k)

/-- A1 one-sided shellwise production bound:
    `P_k ≤ strainSup · Ξ_k`. -/
theorem A1_localized_shell_bound
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ∀ k : Fin K_max,
      localizedProduction (localizedData sad) k
        ≤ sad.strainSup * localizedVortSq (localizedData sad) k := by
  intro k
  simpa [localizedData, toMultiplierData] using
    (localized_shell_bound (localizedData sad) k)

#check @A1_localized_shell_bound_abs
#check @A1_localized_shell_bound

-- ============================================================
-- SECTION 2: A1 -> ABSTRACT ANALYTIC INTERFACES
-- ============================================================

/-- A1 yields the abstract `LocalizedProjectedStretching` interface. -/
theorem A1_to_localizedProjectedStretching
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData sad))
      (strainState sad)
      (toGradientAmplitude (localizedData sad)) := by
  exact localizedProjectedStretching_of_strain_action sad

/-- A1 yields `GradientControlledByStrain` with constant `1`. -/
theorem A1_to_gradientControlledByStrain
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    GradientControlledByStrain
      (strainState sad)
      (toGradientAmplitude (localizedData sad))
      1 := by
  exact gradientControlledByStrain_of_strain_action sad

/-- A1 yields `ProductionFromStrainSup` directly. -/
theorem A1_to_productionFromStrainSup
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData sad))
      (strainState sad) := by
  exact productionFromStrainSup_of_strain_action sad

#check @A1_to_localizedProjectedStretching
#check @A1_to_gradientControlledByStrain
#check @A1_to_productionFromStrainSup

-- ============================================================
-- SECTION 3: PACKAGED A1 THEOREM
-- ============================================================

/-- Packaged capstone theorem for the abstract A1 pipeline.

From shell projector contraction and the shellwise strain-action estimate,
one obtains the full chain needed downstream:

* localized projected stretching,
* gradient controlled by strain,
* production controlled by strain-sup.
-/
theorem A1_full_chain
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    LocalizedProjectedStretching
        (localizedProduction (localizedData sad))
        (strainState sad)
        (toGradientAmplitude (localizedData sad))
      ∧ GradientControlledByStrain
          (strainState sad)
          (toGradientAmplitude (localizedData sad))
          1
      ∧ ProductionFromStrainSup
          (localizedProduction (localizedData sad))
          (strainState sad) := by
  refine ⟨A1_to_localizedProjectedStretching sad, ?_, A1_to_productionFromStrainSup sad⟩
  exact A1_to_gradientControlledByStrain sad

#check @A1_full_chain

-- ============================================================
-- SECTION 4: TORUS-FACING SPECIALIZATION PLACEHOLDER
-- ============================================================

/-- Torus-facing restatement of A1.

This is the abstract theorem that the eventual concrete `T^3` Fourier construction
must instantiate once shell projectors and the pointwise strain-action estimate are
proved on `L²(T^3)^3`.
-/
theorem A1_on_torus_facing
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData sad))
      (strainState sad) := by
  exact A1_to_productionFromStrainSup sad

#check @A1_on_torus_facing

end NSA1Torus
