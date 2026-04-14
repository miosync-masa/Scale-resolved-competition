import NSBarrier.NSFourier
import NSBarrier.NSAnalyticA
import NSBarrier.NSAnalyticA1Locality
import NSBarrier.NSTorusShell
import Mathlib.Tactic

open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality
open NSTorusShell
open scoped InnerProductSpace

namespace NSL2Multiplier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- ============================================================
-- SECTION 1: MULTIPLIER DATA
-- ============================================================

/-- Shellwise multiplier data:
    - `omega k` is ω_k
    - `Z k` is the pre-projection stretching term
    - `Pk k` is the shell projector
    - `gradAmp` is the gradient-type amplitude G
    - `‖Z_k‖ ≤ G · ‖ω_k‖` is the multiplier/locality input. -/
structure ShellMultiplierData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  projData : ShellProjectorData V K_max
  omega : Fin K_max → V
  Z : Fin K_max → V
  gradAmp : ℝ
  gradAmp_nonneg : 0 ≤ gradAmp
  multiplier_le : ∀ k : Fin K_max, ‖Z k‖ ≤ gradAmp * ‖omega k‖

#check @ShellMultiplierData

-- ============================================================
-- SECTION 2: BUILD THE LOCALIZED DATA USED BY A1
-- ============================================================

/-- Turn multiplier data into the `ShellLocalizedData` used by
    `NSAnalyticA1Locality`. -/
def toLocalizedData
    {K_max : ℕ}
    (smd : ShellMultiplierData V K_max) :
    ShellLocalizedData V K_max where
  omega := smd.omega
  Z := smd.Z
  Pk := smd.projData.Pk
  gradAmp := smd.gradAmp
  gradAmp_nonneg := smd.gradAmp_nonneg
  proj_contraction := smd.projData.proj_contraction
  localized_le := by
    intro k
    exact le_trans
      (shellProj_apply_norm_le smd.projData k (smd.Z k))
      (smd.multiplier_le k)

#check @toLocalizedData

/-- The shell-localized production bound follows immediately from the multiplier
    estimate and projector contraction. -/
theorem localized_shell_bound_of_multiplier
    {K_max : ℕ}
    (smd : ShellMultiplierData V K_max) :
    ∀ k : Fin K_max,
      localizedProduction (toLocalizedData smd) k
        ≤ smd.gradAmp * localizedVortSq (toLocalizedData smd) k := by
  intro k
  exact localized_shell_bound (toLocalizedData smd) k

#check @localized_shell_bound_of_multiplier

/-- The abstract `LocalizedProjectedStretching` hypothesis is supplied by the
    multiplier estimate. -/
theorem localizedProjectedStretching_of_multiplier
    {K_max : ℕ}
    (smd : ShellMultiplierData V K_max) (strainSup : ℝ) :
    LocalizedProjectedStretching
      (localizedProduction (toLocalizedData smd))
      (toFourierState_loc (toLocalizedData smd) strainSup)
      (toGradientAmplitude (toLocalizedData smd)) := by
  exact localizedProjectedStretching_of_localized (toLocalizedData smd) strainSup

#check @localizedProjectedStretching_of_multiplier

/-- If `gradAmp ≤ C_str · strainSup`, then the multiplier data induce
    `ProductionFromStrainSup` after rescaling the strain state. -/
theorem productionFromStrainSup_of_multiplier
    {K_max : ℕ}
    (smd : ShellMultiplierData V K_max) (strainSup C_str : ℝ)
    (hgc : smd.gradAmp ≤ C_str * strainSup) :
    let fs := toFourierState_loc (toLocalizedData smd) strainSup
    ProductionFromStrainSup
      (localizedProduction (toLocalizedData smd))
      (rescaledStrainState fs C_str) := by
  simpa [toLocalizedData] using
    (productionFromStrainSup_of_localized
      (toLocalizedData smd) strainSup C_str hgc)

#check @productionFromStrainSup_of_multiplier

end NSL2Multiplier
