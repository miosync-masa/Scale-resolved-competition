import NSBarrier.NSFourier
import NSBarrier.NSPairingBound
import NSBarrier.NSAnalyticA
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

open NSFourier
open NSPairingBound
open NSAnalyticA
open scoped InnerProductSpace

/-!
# Localized Projected Stretch for Shell-Resolved Production

The second Fourier-analytic input:
  P_k = inner(omega_k, (Proj_k . S) omega_k) <= G * Xi_k

where Proj_k is the shell projection and G is a gradient-type amplitude.

## Authors
Masamichi Iizumi, Tamaki Iizumi, Miosync Inc.
-/

namespace NSLocalizedStretch

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

-- SECTION 1: COMPOSITION OPERATOR NORM BOUND

omit [CompleteSpace V] in
/-- Operator norm of composition is bounded by product of norms. -/
theorem opNorm_comp_le
    (A B : V →L[ℝ] V) :
    ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ :=
  ContinuousLinearMap.opNorm_comp_le A B

omit [CompleteSpace V] in
/-- If norm(Proj) <= 1 (orthogonal projection), then norm(Proj . A) <= norm(A). -/
theorem opNorm_comp_le_of_proj_le_one
    (Proj A : V →L[ℝ] V)
    (hP : ‖Proj‖ ≤ 1) :
    ‖Proj.comp A‖ ≤ ‖A‖ := by
  calc ‖Proj.comp A‖
      ≤ ‖Proj‖ * ‖A‖ := opNorm_comp_le Proj A
    _ ≤ 1 * ‖A‖ := by exact mul_le_mul_of_nonneg_right hP (norm_nonneg A)
    _ = ‖A‖ := one_mul ‖A‖

omit [CompleteSpace V] in
/-- Localized pairing: inner(v, (Proj . A) v) <= norm(Proj . A) * norm(v)^2. -/
theorem inner_comp_apply_le
    (Proj A : V →L[ℝ] V) (v : V) :
    ⟪v, (Proj.comp A) v⟫_ℝ ≤ ‖Proj.comp A‖ * ‖v‖ ^ 2 :=
  inner_apply_le_opNorm_mul_sq (Proj.comp A) v

omit [CompleteSpace V] in
/-- Localized bound with explicit amplitude G. -/
theorem inner_comp_apply_le_of_le
    (Proj A : V →L[ℝ] V) (v : V) (G : ℝ)
    (hG : ‖Proj.comp A‖ ≤ G) :
    ⟪v, (Proj.comp A) v⟫_ℝ ≤ G * ‖v‖ ^ 2 :=
  inner_apply_le_of_opNorm_le (Proj.comp A) v G hG

#check @opNorm_comp_le
#check @opNorm_comp_le_of_proj_le_one
#check @inner_comp_apply_le
#check @inner_comp_apply_le_of_le

-- SECTION 2: SHELL-LOCALIZED INSTANTIATION

/-- Shell-localized production data.
    Each shell k has a projection Proj_k and the localized operator
    norm(Proj_k . S) is bounded by gradAmp. -/
structure ShellLocalizedData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  omega : Fin K_max → V
  S : V →L[ℝ] V
  Proj : Fin K_max → (V →L[ℝ] V)
  gradAmp : ℝ
  gradAmp_nonneg : 0 ≤ gradAmp
  localized_le : ∀ k, ‖(Proj k).comp S‖ ≤ gradAmp

/-- Localized shell production: P_k := inner(omega_k, (Proj_k . S)(omega_k)). -/
noncomputable def localizedProduction {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (k : Fin K_max) : ℝ :=
  ⟪sld.omega k, ((sld.Proj k).comp sld.S) (sld.omega k)⟫_ℝ

/-- Localized shell bound: P_k <= gradAmp * norm(omega_k)^2. -/
theorem localized_shell_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    ∀ k : Fin K_max,
      localizedProduction sld k ≤
        sld.gradAmp * ‖sld.omega k‖ ^ 2 := by
  intro k
  exact inner_comp_apply_le_of_le (sld.Proj k) sld.S (sld.omega k)
    sld.gradAmp (sld.localized_le k)

#check @localizedProduction
#check @localized_shell_bound

-- SECTION 3: BRIDGE TO LocalizedProjectedStretching

/-- Construct a FourierState from ShellLocalizedData. -/
noncomputable def toFourierState_loc {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup : ℝ) :
    FourierState K_max where
  shellEnergy := fun k => ‖sld.omega k‖ ^ 2
  shellVorticitySq := fun k => ‖sld.omega k‖ ^ 2
  strainSup := strainSup

/-- Construct a GradientAmplitude from ShellLocalizedData. -/
def toGradientAmplitude {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) :
    GradientAmplitude K_max :=
  fun _ => sld.gradAmp

/-- Bridge: localized shell bound yields LocalizedProjectedStretching. -/
theorem localizedProjectedStretching_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup : ℝ) :
    LocalizedProjectedStretching
      (localizedProduction sld)
      (toFourierState_loc sld strainSup)
      (toGradientAmplitude sld) := by
  intro k
  simp only [toFourierState_loc, toGradientAmplitude]
  exact localized_shell_bound sld k

/-- If gradAmp <= C_str * strainSup, then GradientControlledByStrain holds. -/
theorem gradientControlledByStrain_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup C_str : ℝ)
    (hgc : sld.gradAmp ≤ C_str * strainSup) :
    GradientControlledByStrain
      (toFourierState_loc sld strainSup)
      (toGradientAmplitude sld)
      C_str := by
  simp only [GradientControlledByStrain, toFourierState_loc, toGradientAmplitude]
  exact hgc

/-- Combined: localized bound + gradient-strain control yield
    ProductionFromStrainSup via the rescaled strain state. -/
theorem productionFromStrainSup_of_localized
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {K_max : ℕ}
    (sld : ShellLocalizedData V K_max) (strainSup C_str : ℝ)
    (hgc : sld.gradAmp ≤ C_str * strainSup) :
    ProductionFromStrainSup
      (localizedProduction sld)
      (rescaledStrainState (toFourierState_loc sld strainSup) C_str) := by
  intro k
  have hloc := localized_shell_bound sld k
  have hgc' : sld.gradAmp ≤ C_str * strainSup := hgc
  have hXi : 0 ≤ ‖sld.omega k‖ ^ 2 := by positivity
  simp only [rescaledStrainState, toFourierState_loc]
  calc localizedProduction sld k
      ≤ sld.gradAmp * ‖sld.omega k‖ ^ 2 := hloc
    _ ≤ (C_str * strainSup) * ‖sld.omega k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hgc' hXi

#check @toFourierState_loc
#check @toGradientAmplitude
#check @localizedProjectedStretching_of_localized
#check @gradientControlledByStrain_of_localized
#check @productionFromStrainSup_of_localized

end NSLocalizedStretch
