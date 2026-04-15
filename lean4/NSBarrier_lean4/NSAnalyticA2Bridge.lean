import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSAnalyticA2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSBridge
open NSAnalyticA2

namespace NSAnalyticA2Bridge

-- ============================================================
-- SECTION 1: A2 -> NSFourier
-- ============================================================

/-- Generic bridge: A2 in radius/profile form implies the NSFourier
    shell vorticity-energy bound. -/
theorem bridge_shellVorticityEnergyBound_from_radius
    {K_max : ℕ}
    (fs : FourierState K_max)
    (R2 : RadiusSqProfile K_max)
    (C_shell : ℝ)
    (h0 : ZeroShellVorticity fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs R2)
    (hR : RadiusSqControlledByIndex R2 C_shell) :
    NSFourier.ShellVorticityEnergyBound fs C_shell := by
  exact
    shell_vorticity_energy_bound_from_radius
      fs R2 C_shell h0 hE hXiR hR

/-- Unit-shell specialization with the explicit constant 9/4. -/
theorem bridge_shellVorticityEnergyBound_unit_shell
    {K_max : ℕ}
    (fs : FourierState K_max)
    (h0 : ZeroShellVorticity fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs (unitShellRadiusSq K_max)) :
    NSFourier.ShellVorticityEnergyBound fs (9 / 4 : ℝ) := by
  exact
    shell_vorticity_energy_bound_unit_shell
      fs h0 hE hXiR

/-- Monotone unit-shell specialization: any larger shell constant also works. -/
theorem bridge_shellVorticityEnergyBound_unit_shell_of_le
    {K_max : ℕ}
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hC : (9 / 4 : ℝ) ≤ C_shell)
    (h0 : ZeroShellVorticity fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs (unitShellRadiusSq K_max)) :
    NSFourier.ShellVorticityEnergyBound fs C_shell := by
  exact
    shell_vorticity_energy_bound_unit_shell_of_le
      fs C_shell hC h0 hE hXiR

#check @bridge_shellVorticityEnergyBound_from_radius
#check @bridge_shellVorticityEnergyBound_unit_shell
#check @bridge_shellVorticityEnergyBound_unit_shell_of_le

-- ============================================================
-- SECTION 2: A2 -> NSBridge (direct Fourier bridge)
-- ============================================================

/-- Replace the `ShellVorticityEnergyBound` assumption in
    `bridge_physical_production_closure` by the A2 radius/profile hypotheses. -/
theorem bridge_physical_production_closure_from_radius
    {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hS : 0 ≤ fs.strainSup)
    (hprod : ProductionFromStrainSup sb.P fs)
    (R2 : RadiusSqProfile K_max)
    (h0 : ZeroShellVorticity fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs R2)
    (hR : RadiusSqControlledByIndex R2 C_shell) :
    PhysicalProductionClosure sb (liftedStrainAmplitude fs C_shell) (liftedShellEnergy fs) := by
  apply bridge_physical_production_closure sb fs C_shell hS hprod
  exact bridge_shellVorticityEnergyBound_from_radius fs R2 C_shell h0 hE hXiR hR

/-- Replace the `ShellVorticityEnergyBound` assumption in
    `no_advance_from_fourier_inst` by the A2 radius/profile hypotheses. -/
theorem no_advance_from_fourier_inst_of_radius
    {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_shell : ℝ)
    (hAbarrier : inducedAmplitude fs₂ C_shell ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hS : 0 ≤ fs₂.strainSup)
    (hprod : ProductionFromStrainSup sb₂.P fs₂)
    (R2 : RadiusSqProfile K_max)
    (h0 : ZeroShellVorticity fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hXiR : VorticityControlledByRadiusSq fs₂ R2)
    (hR : RadiusSqControlledByIndex R2 C_shell)
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_from_fourier_inst sb₁ sb₂ fs₂ ν C_shell hAbarrier hS
  · exact hE
  · exact hprod
  · exact bridge_shellVorticityEnergyBound_from_radius fs₂ R2 C_shell h0 hE hXiR hR
  · exact hD

/-- Unit-shell direct bridge into `no_advance_from_fourier_inst`
    with the explicit constant 9/4. -/
theorem no_advance_from_fourier_inst_of_unit_shell
    {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν : ℝ)
    (hAbarrier : inducedAmplitude fs₂ (9 / 4 : ℝ) ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hS : 0 ≤ fs₂.strainSup)
    (hprod : ProductionFromStrainSup sb₂.P fs₂)
    (h0 : ZeroShellVorticity fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hXiR : VorticityControlledByRadiusSq fs₂ (unitShellRadiusSq K_max))
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_from_fourier_inst sb₁ sb₂ fs₂ ν (9 / 4 : ℝ) hAbarrier hS
  · exact hE
  · exact hprod
  · exact bridge_shellVorticityEnergyBound_unit_shell fs₂ h0 hE hXiR
  · exact hD

/-- Monotone unit-shell direct bridge with any `C_shell ≥ 9/4`. -/
theorem no_advance_from_fourier_inst_of_unit_shell_of_le
    {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_shell : ℝ)
    (hAbarrier : inducedAmplitude fs₂ C_shell ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hS : 0 ≤ fs₂.strainSup)
    (hprod : ProductionFromStrainSup sb₂.P fs₂)
    (hC : (9 / 4 : ℝ) ≤ C_shell)
    (h0 : ZeroShellVorticity fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hXiR : VorticityControlledByRadiusSq fs₂ (unitShellRadiusSq K_max))
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_from_fourier_inst sb₁ sb₂ fs₂ ν C_shell hAbarrier hS
  · exact hE
  · exact hprod
  · exact bridge_shellVorticityEnergyBound_unit_shell_of_le fs₂ C_shell hC h0 hE hXiR
  · exact hD

#check @bridge_physical_production_closure_from_radius
#check @no_advance_from_fourier_inst_of_radius
#check @no_advance_from_fourier_inst_of_unit_shell
#check @no_advance_from_fourier_inst_of_unit_shell_of_le

-- ============================================================
-- SECTION 3: A2 -> NSBridge (staged locality bridge)
-- ============================================================

/-- Replace the `ShellVorticityEnergyBound` assumption in
    `physical_production_closure_from_locality` by the A2 radius/profile hypotheses. -/
theorem physical_production_closure_from_locality_of_radius
    {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str C_shell : ℝ)
    (hXi : NSFourier.ShellVorticitySqNonneg fs)
    (hS : 0 ≤ fs.strainSup)
    (hCstr : 0 ≤ C_str)
    (hloc : LocalizedProductionFromGradient sb fs G)
    (hgc : GradientControlledByStrain fs G C_str)
    (R2 : RadiusSqProfile K_max)
    (h0 : ZeroShellVorticity fs)
    (hE : NSFourier.ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs R2)
    (hR : RadiusSqControlledByIndex R2 C_shell) :
    PhysicalProductionClosure sb
      (liftedStrainAmplitude fs (C_str * C_shell))
      (liftedShellEnergy fs) := by
  apply physical_production_closure_from_locality
    sb fs G C_str C_shell hXi hS hCstr hloc hgc
  exact bridge_shellVorticityEnergyBound_from_radius fs R2 C_shell h0 hE hXiR hR

/-- Replace the `ShellVorticityEnergyBound` assumption in
    `no_advance_physical_from_locality_inst` by the A2 radius/profile hypotheses. -/
theorem no_advance_physical_from_locality_inst_of_radius
    {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_str C_shell : ℝ)
    (G : GradientAmplitude K_max)
    (hAbarrier :
      inducedAmplitude fs₂ (C_str * C_shell) ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hXi : NSFourier.ShellVorticitySqNonneg fs₂)
    (hS : 0 ≤ fs₂.strainSup)
    (hCstr : 0 ≤ C_str)
    (h0 : ZeroShellVorticity fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hloc : LocalizedProductionFromGradient sb₂ fs₂ G)
    (hgc : GradientControlledByStrain fs₂ G C_str)
    (R2 : RadiusSqProfile K_max)
    (hXiR : VorticityControlledByRadiusSq fs₂ R2)
    (hR : RadiusSqControlledByIndex R2 C_shell)
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical_from_locality_inst
    sb₁ sb₂ fs₂ ν C_str C_shell G
  · exact hAbarrier
  · exact hXi
  · exact hS
  · exact hCstr
  · exact hE
  · exact hloc
  · exact hgc
  · exact bridge_shellVorticityEnergyBound_from_radius fs₂ R2 C_shell h0 hE hXiR hR
  · exact hD

/-- Unit-shell staged-locality bridge with explicit constant 9/4. -/
theorem no_advance_physical_from_locality_inst_of_unit_shell
    {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_str : ℝ)
    (G : GradientAmplitude K_max)
    (hAbarrier :
      inducedAmplitude fs₂ (C_str * (9 / 4 : ℝ)) ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hXi : NSFourier.ShellVorticitySqNonneg fs₂)
    (hS : 0 ≤ fs₂.strainSup)
    (hCstr : 0 ≤ C_str)
    (h0 : ZeroShellVorticity fs₂)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hloc : LocalizedProductionFromGradient sb₂ fs₂ G)
    (hgc : GradientControlledByStrain fs₂ G C_str)
    (hXiR : VorticityControlledByRadiusSq fs₂ (unitShellRadiusSq K_max))
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical_from_locality_inst
    sb₁ sb₂ fs₂ ν C_str (9 / 4 : ℝ) G
  · exact hAbarrier
  · exact hXi
  · exact hS
  · exact hCstr
  · exact hE
  · exact hloc
  · exact hgc
  · exact bridge_shellVorticityEnergyBound_unit_shell fs₂ h0 hE hXiR
  · exact hD

#check @physical_production_closure_from_locality_of_radius
#check @no_advance_physical_from_locality_inst_of_radius
#check @no_advance_physical_from_locality_inst_of_unit_shell

end NSAnalyticA2Bridge
