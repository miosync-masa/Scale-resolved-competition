import NSBarrier.NSFourier
import NSBarrier.NSAnalyticA
import NSBarrier.NSAnalyticA1Pairing
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open NSFourier
open NSAnalyticA
open NSAnalyticA1Pairing
open scoped InnerProductSpace

/-!
# Localized Projected Stretch for Shell-Resolved Production

Lightweight `LinearMap`-based locality layer for A1.

This file isolates the genuinely Fourier-analytic input:

  ‖Pk Zk‖ ≤ G · ‖ωk‖

from the abstract pairing bound

  |⟪ωk, Pk Zk⟫| ≤ ‖ωk‖ · ‖Pk Zk‖

and turns them into the shellwise production estimate

  |P_k| ≤ G · ‖ωk‖²

which then feeds into `LocalizedProjectedStretching`,
`GradientControlledByStrain`, and finally `ProductionFromStrainSup`.
-/

namespace NSAnalyticA1Locality

-- ============================================================
-- SECTION 1: LOCALIZED SHELL DATA
-- ============================================================

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Shell-localized production data:
    - `omega k` is the shell vorticity component ω_k
    - `Z k` is the projected stretching input before the final pairing
    - `Pk k` is the shell projection / shell-local operator acting on `Z k`
    - `gradAmp` is the gradient-type amplitude G

    The intended estimate is
      ‖Pk(k) (Z(k))‖ ≤ gradAmp · ‖omega(k)‖
    for each shell `k`. -/
structure ShellLocalizedData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  omega : Fin K_max → V
  Z : Fin K_max → V
  Pk : Fin K_max → (V →ₗ[ℝ] V)
  gradAmp : ℝ
  gradAmp_nonneg : 0 ≤ gradAmp
  proj_contraction : ∀ k, ProjectionContraction (Pk k)
  localized_le : ∀ k, ‖(Pk k) (Z k)‖ ≤ gradAmp * ‖omega k‖

#check @ShellLocalizedData

/-- Shell-localized pairing production:
    P_k := ⟪ω_k, P_k Z_k⟫. -/
noncomputable def localizedProduction
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (k : Fin K_max) : ℝ :=
  ⟪sld.omega k, (sld.Pk k) (sld.Z k)⟫_ℝ

/-- Shell-localized squared vorticity:
    Ξ_k := ‖ω_k‖². -/
noncomputable def localizedVortSq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (k : Fin K_max) : ℝ :=
  ‖sld.omega k‖ ^ 2

#check @localizedProduction
#check @localizedVortSq

-- ============================================================
-- SECTION 2: PAIRING + LOCALITY => SHELL BOUND
-- ============================================================

/-- Abstract pairing bound specialized to shell-localized data:
    |P_k| ≤ ‖ω_k‖ · ‖Pk Z_k‖. -/
theorem pairing_bound_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ∀ k : Fin K_max,
      |localizedProduction sld k| ≤ ‖sld.omega k‖ * ‖(sld.Pk k) (sld.Z k)‖ := by
  intro k
  unfold localizedProduction
  exact shell_production_pairing_bound (sld.Pk k) (sld.omega k) (sld.Z k)

/-- Core localized shell bound:
    if ‖Pk Z_k‖ ≤ G · ‖ω_k‖ then |P_k| ≤ G · ‖ω_k‖². -/
theorem localized_shell_bound_abs
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ∀ k : Fin K_max,
      |localizedProduction sld k| ≤ sld.gradAmp * localizedVortSq sld k := by
  intro k
  have hpair :
      |localizedProduction sld k| ≤ ‖sld.omega k‖ * ‖(sld.Pk k) (sld.Z k)‖ :=
    pairing_bound_localized sld k
  have hloc : ‖(sld.Pk k) (sld.Z k)‖ ≤ sld.gradAmp * ‖sld.omega k‖ :=
    sld.localized_le k
  have hnorm_nonneg : 0 ≤ ‖sld.omega k‖ := norm_nonneg (sld.omega k)
  have hmul :
      ‖sld.omega k‖ * ‖(sld.Pk k) (sld.Z k)‖
        ≤ ‖sld.omega k‖ * (sld.gradAmp * ‖sld.omega k‖) := by
    exact mul_le_mul_of_nonneg_left hloc hnorm_nonneg
  have hsq :
      ‖sld.omega k‖ * (sld.gradAmp * ‖sld.omega k‖)
        = sld.gradAmp * localizedVortSq sld k := by
    unfold localizedVortSq
    ring
  exact le_trans hpair (by simpa [hsq] using hmul)

/-- One-sided shell bound, dropping the absolute value:
    P_k ≤ G · Ξ_k. -/
theorem localized_shell_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ∀ k : Fin K_max,
      localizedProduction sld k ≤ sld.gradAmp * localizedVortSq sld k := by
  intro k
  exact le_trans (le_abs_self (localizedProduction sld k)) (localized_shell_bound_abs sld k)

theorem localizedVortSq_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ∀ k, 0 ≤ localizedVortSq sld k := by
  intro k
  unfold localizedVortSq
  positivity

#check @pairing_bound_localized
#check @localized_shell_bound_abs
#check @localized_shell_bound
#check @localizedVortSq_nonneg

-- ============================================================
-- SECTION 3: BRIDGE TO NSAnalyticA
-- ============================================================

/-- Turn shell-localized data into a FourierState by identifying
    shell energy and shell vorticity square with ‖ω_k‖²,
    and leaving strainSup as an external parameter. -/
noncomputable def toFourierState_loc
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup : ℝ) : FourierState K_max where
  shellEnergy := localizedVortSq sld
  shellVorticitySq := localizedVortSq sld
  strainSup := strainSup

/-- The gradient amplitude induced by shell-localized data. -/
def toGradientAmplitude
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) : GradientAmplitude K_max :=
  fun _ => sld.gradAmp

theorem toFourierState_loc_shellEnergy_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ShellEnergyNonneg (toFourierState_loc sld 0) := by
  intro k
  exact localizedVortSq_nonneg sld k

theorem toFourierState_loc_shellVorticitySq_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ShellVorticitySqNonneg (toFourierState_loc sld 0) := by
  intro k
  exact localizedVortSq_nonneg sld k

/-- Bridge from the shell-localized estimate to `LocalizedProjectedStretching`. -/
theorem localizedProjectedStretching_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup : ℝ) :
    LocalizedProjectedStretching
      (localizedProduction sld)
      (toFourierState_loc sld strainSup)
      (toGradientAmplitude sld) := by
  intro k
  simp only [toGradientAmplitude, toFourierState_loc, localizedVortSq]
  exact localized_shell_bound sld k

/-- If gradAmp ≤ C_str · strainSup, then `GradientControlledByStrain` holds. -/
theorem gradientControlledByStrain_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup C_str : ℝ)
    (hgc : sld.gradAmp ≤ C_str * strainSup) :
    GradientControlledByStrain
      (toFourierState_loc sld strainSup)
      (toGradientAmplitude sld)
      C_str := by
  simp only [GradientControlledByStrain, toGradientAmplitude, toFourierState_loc]
  exact hgc

/-- Combined bridge:
    shell-localized production + strain control yield `ProductionFromStrainSup`
    for the rescaled strain state. -/
theorem productionFromStrainSup_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup C_str : ℝ)
    (hgc : sld.gradAmp ≤ C_str * strainSup) :
    ProductionFromStrainSup
      (localizedProduction sld)
      (rescaledStrainState (toFourierState_loc sld strainSup) C_str) := by
  intro k
  have hloc := localized_shell_bound sld k
  have hXi : 0 ≤ localizedVortSq sld k := localizedVortSq_nonneg sld k
  simp only [rescaledStrainState, toFourierState_loc, localizedVortSq]
  calc
    localizedProduction sld k
      ≤ sld.gradAmp * ‖sld.omega k‖ ^ 2 := hloc
    _ ≤ (C_str * strainSup) * ‖sld.omega k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hgc hXi

#check @toFourierState_loc
#check @toGradientAmplitude
#check @toFourierState_loc_shellEnergy_nonneg
#check @toFourierState_loc_shellVorticitySq_nonneg
#check @localizedProjectedStretching_of_localized
#check @gradientControlledByStrain_of_localized
#check @productionFromStrainSup_of_localized

end NSAnalyticA1Locality
