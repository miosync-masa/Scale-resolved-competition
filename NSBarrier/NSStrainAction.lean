import NSBarrier.NSFourier
import NSBarrier.NSAnalyticA
import NSBarrier.NSTorusShell
import NSBarrier.NSAnalyticA1Locality
import NSBarrier.NSL2Multiplier
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open NSFourier
open NSAnalyticA
open NSTorusShell
open NSAnalyticA1Locality
open NSL2Multiplier
open scoped InnerProductSpace

namespace NSStrainAction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- ============================================================
-- SECTION 1: STRAIN-ACTION DATA
-- ============================================================

/-- Shellwise strain-action data.

`omega k` is the shell vorticity component `ω_k`.
`Z k` is the shellwise stretching term before projection.
`projData` supplies the shell projector family.
`strainSup` is the shell-independent strain amplitude.
`action_le` is the pointwise / multiplier input:
  ‖Z_k‖ ≤ strainSup · ‖ω_k‖.
-/
structure ShellStrainActionData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  projData : ShellProjectorData V K_max
  omega : Fin K_max → V
  Z : Fin K_max → V
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  action_le : ∀ k : Fin K_max, ‖Z k‖ ≤ strainSup * ‖omega k‖

#check @ShellStrainActionData

-- ============================================================
-- SECTION 2: REDUCTION TO MULTIPLIER DATA
-- ============================================================

/-- Turn shellwise strain-action data into the multiplier data used in
`NSL2Multiplier`, with `gradAmp = strainSup`. -/
def toMultiplierData
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ShellMultiplierData V K_max where
  projData := sad.projData
  omega := sad.omega
  Z := sad.Z
  gradAmp := sad.strainSup
  gradAmp_nonneg := sad.strainSup_nonneg
  multiplier_le := sad.action_le

/-- The corresponding localized shell data. -/
noncomputable def localizedData
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ShellLocalizedData V K_max :=
  toLocalizedData (toMultiplierData sad)

/-- The corresponding Fourier state with strain amplitude `strainSup`. -/
noncomputable def strainState
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    FourierState K_max :=
  toFourierState_loc (localizedData sad) sad.strainSup

#check @toMultiplierData
#check @localizedData
#check @strainState

-- ============================================================
-- SECTION 3: LOCALIZED PROJECTED STRETCHING
-- ============================================================

/-- The shellwise strain-action input directly yields
`LocalizedProjectedStretching`. -/
theorem localizedProjectedStretching_of_strain_action
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData sad))
      (strainState sad)
      (toGradientAmplitude (localizedData sad)) := by
  exact localizedProjectedStretching_of_multiplier
    (toMultiplierData sad)
    sad.strainSup

/-- Since `gradAmp = strainSup`, the gradient is controlled by strain with constant `1`. -/
theorem gradientControlledByStrain_of_strain_action
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    GradientControlledByStrain
      (strainState sad)
      (toGradientAmplitude (localizedData sad))
      1 := by
  simp [GradientControlledByStrain, strainState, localizedData, toLocalizedData,
    toMultiplierData, toGradientAmplitude, toFourierState_loc]

#check @localizedProjectedStretching_of_strain_action
#check @gradientControlledByStrain_of_strain_action

-- ============================================================
-- SECTION 4: BRIDGE TO ProductionFromStrainSup
-- ============================================================

/-- First rescaled form: the multiplier theorem yields `ProductionFromStrainSup`
for the `C_str = 1` rescaling of the strain state. -/
theorem productionFromStrainSup_of_strain_action_rescaled
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    let fs := strainState sad
    ProductionFromStrainSup
      (localizedProduction (localizedData sad))
      (rescaledStrainState fs 1) := by
  simpa [strainState, localizedData, toMultiplierData] using
    (productionFromStrainSup_of_multiplier
      (toMultiplierData sad)
      sad.strainSup
      1
      (by simp [toMultiplierData]))

/-- Since rescaling by `1` leaves the strain state unchanged,
the previous theorem simplifies to a direct `ProductionFromStrainSup` statement. -/
theorem productionFromStrainSup_of_strain_action
    {K_max : ℕ}
    (sad : ShellStrainActionData V K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData sad))
      (strainState sad) := by
  simpa [rescaledStrainState, strainState] using
    (productionFromStrainSup_of_strain_action_rescaled sad)

#check @productionFromStrainSup_of_strain_action_rescaled
#check @productionFromStrainSup_of_strain_action

end NSStrainAction
