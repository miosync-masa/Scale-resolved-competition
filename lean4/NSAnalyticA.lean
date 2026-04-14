import NSBarrier.Basic
import NSBarrier.NSFourier
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier

namespace NSAnalyticA

/-- Auxiliary gradient-type amplitude, intended to model ‖∇v‖∞ or a comparable
    shellwise stretching amplitude. -/
def GradientAmplitude (K_max : ℕ) := FourierState K_max → ℝ

/-- A shellwise radius-squared profile R²(k), intended to model an upper shell radius
    bound such as sup_{|κ|≈k} |κ|². -/
def RadiusSqProfile (K_max : ℕ) := Fin K_max → ℝ

/-- Localized shellwise production bound:
    P_k ≤ G(fs) · Ξ_k.
    This is the post-localized form of the projected stretching estimate. -/
def LocalizedProjectedStretching {K_max : ℕ}
    (P_shell : Fin K_max → ℝ)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max) : Prop :=
  ∀ k : Fin K_max, P_shell k ≤ G fs * fs.shellVorticitySq k

/-- Control of the gradient-type amplitude by strain-sup:
    G(fs) ≤ C_str · strainSup(fs). -/
def GradientControlledByStrain {K_max : ℕ}
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str : ℝ) : Prop :=
  G fs ≤ C_str * fs.strainSup

/-- Shellwise vorticity is controlled by a radius-squared profile:
    Ξ_k ≤ R²(k) · E_k. -/
def VorticityControlledByRadiusSq {K_max : ℕ}
    (fs : FourierState K_max)
    (R2 : RadiusSqProfile K_max) : Prop :=
  ∀ k : Fin K_max, fs.shellVorticitySq k ≤ R2 k * fs.shellEnergy k

/-- The radius-squared profile is controlled by shell index:
    R²(k) ≤ C_shell · k². -/
def RadiusSqControlledByIndex {K_max : ℕ}
    (R2 : RadiusSqProfile K_max)
    (C_shell : ℝ) : Prop :=
  ∀ k : Fin K_max, R2 k ≤ C_shell * (k.val : ℝ) ^ 2

/-- Rescale the strain amplitude inside a Fourier state by a constant C_str. -/
def rescaledStrainState {K_max : ℕ}
    (fs : FourierState K_max)
    (C_str : ℝ) : FourierState K_max :=
  { fs with strainSup := C_str * fs.strainSup }

/-- Lift Fourier shell energy into the barrier-side ShellEnergy type. -/
def liftedShellEnergy {K_max : ℕ}
    (fs : FourierState K_max) : ShellEnergy K_max :=
  fun _ k => fs.shellEnergy k

/-- Lift a constant Fourier-side amplitude into the barrier-side StrainAmplitude type. -/
def liftedStrainAmplitude {K_max : ℕ}
    (fs : FourierState K_max) (C : ℝ) : StrainAmplitude K_max :=
  fun _ => inducedAmplitude fs C

/-- Barrier-side nonnegativity of lifted shell energy from Fourier-side nonnegativity. -/
theorem liftedShellEnergy_nonneg {K_max : ℕ}
    (fs : FourierState K_max)
    (hE : NSFourier.ShellEnergyNonneg fs) :
    _root_.ShellEnergyNonneg (liftedShellEnergy fs) := by
  intro _ k
  exact hE k

/-- Barrier-side dissipation closure from Fourier-side dissipation-from-energy. -/
theorem liftedDissipationClosure {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (ν : ℝ)
    (hD : DissipationFromEnergy sb.D ν fs) :
    PhysicalDissipationClosure sb ν (liftedShellEnergy fs) := by
  intro k
  exact hD k

/-- Lemma A, staged form:
    localized projected production plus gradient-to-strain control implies a
    shellwise strain-sup production estimate. -/
theorem production_from_localized_gradient_to_strain {K_max : ℕ}
    (P_shell : Fin K_max → ℝ)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str : ℝ)
    (hXi : NSFourier.ShellVorticitySqNonneg fs)
    (hloc : LocalizedProjectedStretching P_shell fs G)
    (hgc : GradientControlledByStrain fs G C_str) :
    ProductionFromStrainSup P_shell (rescaledStrainState fs C_str) := by
  intro k
  have hPk : P_shell k ≤ G fs * fs.shellVorticitySq k := hloc k
  have hXik : 0 ≤ fs.shellVorticitySq k := hXi k
  have hcoef : G fs ≤ C_str * fs.strainSup := hgc
  have hmul :
      G fs * fs.shellVorticitySq k ≤
      (C_str * fs.strainSup) * fs.shellVorticitySq k := by
    exact mul_le_mul_of_nonneg_right hcoef hXik
  exact le_trans hPk (by simpa [rescaledStrainState] using hmul)

/-- Lemma B, staged form:
    shell vorticity-energy bound from a radius-squared shell profile. -/
theorem shell_vorticity_energy_bound_from_radius {K_max : ℕ}
    (fs : FourierState K_max)
    (R2 : RadiusSqProfile K_max)
    (C_shell : ℝ)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hVR : VorticityControlledByRadiusSq fs R2)
    (hR2 : RadiusSqControlledByIndex R2 C_shell) :
    ShellVorticityEnergyBound fs C_shell := by
  intro k
  have hXiR : fs.shellVorticitySq k ≤ R2 k * fs.shellEnergy k := hVR k
  have hRk : R2 k ≤ C_shell * (k.val : ℝ) ^ 2 := hR2 k
  have hEk : 0 ≤ fs.shellEnergy k := hE k
  have hmul : R2 k * fs.shellEnergy k ≤ (C_shell * (k.val : ℝ) ^ 2) * fs.shellEnergy k := by
    exact mul_le_mul_of_nonneg_right hRk hEk
  exact le_trans hXiR hmul

/-- Combined closure theorem from analytic A-type hypotheses:
    localized production + strain control + shell radius control imply the
    barrier-side physical production closure. -/
theorem physical_production_closure_from_analytic_A {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (R2 : RadiusSqProfile K_max)
    (C_str C_shell : ℝ)
    (hXi : NSFourier.ShellVorticitySqNonneg fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hS : 0 ≤ fs.strainSup)
    (hCstr : 0 ≤ C_str)
    (hloc : LocalizedProjectedStretching sb.P fs G)
    (hgc : GradientControlledByStrain fs G C_str)
    (hVR : VorticityControlledByRadiusSq fs R2)
    (hR2 : RadiusSqControlledByIndex R2 C_shell) :
    PhysicalProductionClosure sb
      (liftedStrainAmplitude fs (C_str * C_shell))
      (liftedShellEnergy fs) := by
  have hprod :
      ProductionFromStrainSup sb.P (rescaledStrainState fs C_str) :=
    production_from_localized_gradient_to_strain sb.P fs G C_str hXi hloc hgc
  have hXiE : ShellVorticityEnergyBound fs C_shell :=
    shell_vorticity_energy_bound_from_radius fs R2 C_shell hE hVR hR2
  have hS' : 0 ≤ (rescaledStrainState fs C_str).strainSup := by
    dsimp [rescaledStrainState]
    nlinarith [hS, hCstr]
  intro k
  have hk := NSFourier.physical_production_closure_inst
      sb.P (rescaledStrainState fs C_str) C_shell hS' hprod hXiE k
  simpa [liftedStrainAmplitude, liftedShellEnergy, rescaledStrainState,
    NSFourier.inducedAmplitude, mul_assoc, mul_left_comm, mul_comm]
    using hk

/-- Final A-layer consequence:
    once the analytic A-type closure is available and the front threshold condition
    holds, no corridor advance is possible. -/
theorem no_advance_from_analytic_A {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_str C_shell : ℝ)
    (G : GradientAmplitude K_max)
    (R2 : RadiusSqProfile K_max)
    (hAbarrier :
      inducedAmplitude fs₂ (C_str * C_shell) ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hXi : NSFourier.ShellVorticitySqNonneg fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hS : 0 ≤ fs₂.strainSup)
    (hCstr : 0 ≤ C_str)
    (hloc : LocalizedProjectedStretching sb₂.P fs₂ G)
    (hgc : GradientControlledByStrain fs₂ G C_str)
    (hVR : VorticityControlledByRadiusSq fs₂ R2)
    (hR2 : RadiusSqControlledByIndex R2 C_shell)
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical
    sb₁ sb₂ ν
    (liftedStrainAmplitude fs₂ (C_str * C_shell))
    (liftedShellEnergy fs₂)
  · simpa [liftedStrainAmplitude, NSFourier.inducedAmplitude,
      mul_assoc, mul_left_comm, mul_comm] using hAbarrier
  · exact liftedShellEnergy_nonneg fs₂ hE
  · exact
      physical_production_closure_from_analytic_A
        sb₂ fs₂ G R2 C_str C_shell hXi hE hS hCstr hloc hgc hVR hR2
  · exact liftedDissipationClosure sb₂ fs₂ ν hD

#check @GradientAmplitude
#check @RadiusSqProfile
#check @LocalizedProjectedStretching
#check @GradientControlledByStrain
#check @VorticityControlledByRadiusSq
#check @RadiusSqControlledByIndex
#check @rescaledStrainState
#check @liftedShellEnergy
#check @liftedStrainAmplitude
#check @production_from_localized_gradient_to_strain
#check @shell_vorticity_energy_bound_from_radius
#check @physical_production_closure_from_analytic_A
#check @no_advance_from_analytic_A

end NSAnalyticA
