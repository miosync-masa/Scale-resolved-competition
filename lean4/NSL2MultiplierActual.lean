import NSBarrier.NSFourier
import NSBarrier.NSTorusShell
import NSBarrier.NSTorusShellModes
import NSBarrier.NSAnalyticA
import NSBarrier.NSAnalyticA1Locality
import NSBarrier.NSStrainAction
import Mathlib.Tactic

open NSFourier
open NSTorusShell
open NSTorusShellActual
open NSTorusShellModes
open NSAnalyticA
open NSAnalyticA1Locality
open NSStrainAction
open scoped InnerProductSpace

namespace NSL2MultiplierActual

-- `InnerProductSpace ℝ L2T3` is not an instance in Mathlib (rclikeToReal is a
-- reducible non-instance to avoid diamonds). We provide it here.
noncomputable instance : InnerProductSpace ℝ L2T3 :=
  InnerProductSpace.rclikeToReal ℂ L2T3

-- ℂ-linear maps on L2T3 can be restricted to ℝ-linear maps.
instance : LinearMap.CompatibleSMul L2T3 L2T3 ℝ ℂ where
  map_smul fₗ r x := fₗ.map_smul (r : ℂ) x

-- ============================================================
-- SECTION 1: ACTUAL SHELL PROJECTOR DATA ON T³
-- ============================================================

/-- The actual shell projector, viewed as an `ℝ`-linear continuous map. -/
noncomputable def realShellProj {K_max : ℕ} (k : Fin K_max) :
    L2T3 →L[ℝ] L2T3 :=
  (actualShellProjFamily (K_max := K_max) k).restrictScalars ℝ

/-- The actual shell projector family on `L²(T³)`, viewed as an `ℝ`-linear
    projector family so that it can feed into the existing `ShellStrainActionData`
    pipeline. -/
noncomputable def actualShellProjectorData {K_max : ℕ} :
    ShellProjectorData L2T3 K_max where
  Pk := fun k => (realShellProj (K_max := K_max) k).toLinearMap
  proj_contraction := by
    intro k z
    simpa [realShellProj] using
      (actualShellProjFamily_contraction (K_max := K_max) k z)

#check @realShellProj
#check @actualShellProjectorData

-- ============================================================
-- SECTION 2: ACTUAL STRAIN-ACTION DATA
-- ============================================================

/-- Actual shell strain-action data on scalar complex `L²(T³)`:
    - `omega k` is the shell vorticity component ω_k
    - `Z k` is the shellwise stretching term before projection
    - `strainSup` is the shell-independent amplitude
    - `action_le` is the actual multiplier bound
      ‖Z_k‖ ≤ strainSup · ‖ω_k‖. -/
structure ActualShellStrainActionData (K_max : ℕ) where
  omega : Fin K_max → L2T3
  Z : Fin K_max → L2T3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  action_le : ∀ k : Fin K_max, ‖Z k‖ ≤ strainSup * ‖omega k‖

#check @ActualShellStrainActionData

/-- Convert actual torus data into the abstract shell strain-action data. -/
noncomputable def toShellStrainActionData {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    ShellStrainActionData L2T3 K_max where
  projData := actualShellProjectorData (K_max := K_max)
  omega := sad.omega
  Z := sad.Z
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  action_le := sad.action_le

#check @toShellStrainActionData

-- ============================================================
-- SECTION 3: ACTUAL LOCALIZED DATA AND FOURIER STATE
-- ============================================================

/-- The actual localized shell data induced by `ActualShellStrainActionData`. -/
noncomputable def actualLocalizedData {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    ShellLocalizedData L2T3 K_max :=
  NSStrainAction.localizedData (toShellStrainActionData sad)

/-- The actual Fourier state induced by `ActualShellStrainActionData`. -/
noncomputable def actualStrainState {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    FourierState K_max :=
  NSStrainAction.strainState (toShellStrainActionData sad)

#check @actualLocalizedData
#check @actualStrainState

-- ============================================================
-- SECTION 4: ACTUAL TORUS MULTIPLIER -> LOCALIZED PROJECTED STRETCHING
-- ============================================================

/-- The actual strain-action hypothesis yields `LocalizedProjectedStretching`
    on the actual torus shell projector family. -/
theorem localizedProjectedStretching_of_actual_strain_action
    {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    LocalizedProjectedStretching
      (localizedProduction (actualLocalizedData sad))
      (actualStrainState sad)
      (toGradientAmplitude (actualLocalizedData sad)) := by
  simpa [actualLocalizedData, actualStrainState] using
    (NSStrainAction.localizedProjectedStretching_of_strain_action
      (toShellStrainActionData sad))

/-- Since the actual multiplier uses `gradAmp = strainSup`,
    `GradientControlledByStrain` holds with constant `1`. -/
theorem gradientControlledByStrain_of_actual_strain_action
    {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    GradientControlledByStrain
      (actualStrainState sad)
      (toGradientAmplitude (actualLocalizedData sad))
      1 := by
  simpa [actualLocalizedData, actualStrainState] using
    (NSStrainAction.gradientControlledByStrain_of_strain_action
      (toShellStrainActionData sad))

#check @localizedProjectedStretching_of_actual_strain_action
#check @gradientControlledByStrain_of_actual_strain_action

-- ============================================================
-- SECTION 5: ACTUAL TORUS MULTIPLIER -> ProductionFromStrainSup
-- ============================================================

/-- First rescaled form: the actual multiplier theorem yields
    `ProductionFromStrainSup` for the `C_str = 1` rescaling of the actual strain state. -/
theorem productionFromStrainSup_of_actual_strain_action_rescaled
    {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    ProductionFromStrainSup
      (localizedProduction (actualLocalizedData sad))
      (rescaledStrainState (actualStrainState sad) 1) := by
  simpa [actualLocalizedData, actualStrainState] using
    (NSStrainAction.productionFromStrainSup_of_strain_action_rescaled
      (toShellStrainActionData sad))

/-- Since rescaling by `1` leaves the strain state unchanged,
    the actual torus multiplier bound yields a direct `ProductionFromStrainSup`
    statement. -/
theorem productionFromStrainSup_of_actual_strain_action
    {K_max : ℕ}
    (sad : ActualShellStrainActionData K_max) :
    ProductionFromStrainSup
      (localizedProduction (actualLocalizedData sad))
      (actualStrainState sad) := by
  simpa [actualLocalizedData, actualStrainState, rescaledStrainState] using
    (productionFromStrainSup_of_actual_strain_action_rescaled sad)

#check @productionFromStrainSup_of_actual_strain_action_rescaled
#check @productionFromStrainSup_of_actual_strain_action

end NSL2MultiplierActual
