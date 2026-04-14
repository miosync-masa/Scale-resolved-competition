import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# NSFourier
Fourier-side analytic interface for shellwise Navier–Stokes estimates.

This file contains no axioms.
Instead, the Fourier-side analytic statements are represented as Props,
and downstream files consume them as hypotheses.
-/

namespace NSFourier

/-- Abstract Fourier-side state attached to a finite shell model. -/
structure FourierState (K_max : ℕ) where
  /-- shell energy E_k ≈ Σ_{|κ|≈k} |v̂(κ)|² -/
  shellEnergy : Fin K_max → ℝ
  /-- shell vorticity size Ξ_k ≈ ‖ω_k‖²_{L²} -/
  shellVorticitySq : Fin K_max → ℝ
  /-- strain amplitude A ≈ ‖S‖∞ -/
  strainSup : ℝ

/-- Nonnegativity of shell energy. -/
def ShellEnergyNonneg {K_max : ℕ} (fs : FourierState K_max) : Prop :=
  ∀ k, 0 ≤ fs.shellEnergy k

/-- Nonnegativity of shellwise vorticity size. -/
def ShellVorticitySqNonneg {K_max : ℕ} (fs : FourierState K_max) : Prop :=
  ∀ k, 0 ≤ fs.shellVorticitySq k

/-- Shellwise vorticity-energy comparison:
    Ξ_k ≤ C_shell · k² · E_k. -/
def ShellVorticityEnergyBound {K_max : ℕ}
    (fs : FourierState K_max) (C_shell : ℝ) : Prop :=
  ∀ k : Fin K_max,
    fs.shellVorticitySq k ≤ C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k

/-- Shellwise production controlled by strain-sup:
    P_k ≤ ‖S‖∞ · Ξ_k. -/
def ProductionFromStrainSup {K_max : ℕ}
    (P_shell : Fin K_max → ℝ)
    (fs : FourierState K_max) : Prop :=
  ∀ k : Fin K_max,
    P_shell k ≤ fs.strainSup * fs.shellVorticitySq k

/-- Shellwise dissipation lower bound:
    ν · k⁴ · E_k ≤ D_k. -/
def DissipationFromEnergy {K_max : ℕ}
    (D_shell : Fin K_max → ℝ)
    (ν : ℝ)
    (fs : FourierState K_max) : Prop :=
  ∀ k : Fin K_max,
    ν * (k.val : ℝ) ^ 4 * fs.shellEnergy k ≤ D_shell k

/-- Induced physical drive amplitude A = C_shell · ‖S‖∞. -/
def inducedAmplitude {K_max : ℕ}
    (fs : FourierState K_max) (C_shell : ℝ) : ℝ :=
  fs.strainSup * C_shell

/-- Identity theorem form of the production hypothesis.
    This replaces the old axiom by an explicit assumption. -/
theorem physical_production_from_strain_sup
    {K_max : ℕ}
    (P_shell : Fin K_max → ℝ)
    (fs : FourierState K_max)
    (hprod : ProductionFromStrainSup P_shell fs) :
    ProductionFromStrainSup P_shell fs := hprod

/-- Identity theorem form of the shell vorticity-energy hypothesis.
    This replaces the old axiom by an explicit assumption. -/
theorem shell_vorticity_energy_bound
    {K_max : ℕ}
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hXiE : ShellVorticityEnergyBound fs C_shell) :
    ShellVorticityEnergyBound fs C_shell := hXiE

/-- Closure lemma combining the two analytic inputs:
    P_k ≤ (C_shell · ‖S‖∞) · k² · E_k. -/
theorem physical_production_closure_inst
    {K_max : ℕ}
    (P_shell : Fin K_max → ℝ)
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hS : 0 ≤ fs.strainSup)
    (hprod : ProductionFromStrainSup P_shell fs)
    (hXiE : ShellVorticityEnergyBound fs C_shell) :
    ∀ k : Fin K_max,
      P_shell k ≤ inducedAmplitude fs C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k := by
  intro k
  have hPk : P_shell k ≤ fs.strainSup * fs.shellVorticitySq k := hprod k
  have hXi : fs.shellVorticitySq k ≤ C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k := hXiE k
  have hmul :
      fs.strainSup * fs.shellVorticitySq k ≤
      fs.strainSup * (C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k) := by
    exact mul_le_mul_of_nonneg_left hXi hS
  calc
    P_shell k ≤ fs.strainSup * fs.shellVorticitySq k := hPk
    _ ≤ fs.strainSup * (C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k) := hmul
    _ = inducedAmplitude fs C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k := by
      unfold inducedAmplitude
      ring

#check @FourierState
#check @ShellEnergyNonneg
#check @ShellVorticitySqNonneg
#check @ShellVorticityEnergyBound
#check @ProductionFromStrainSup
#check @DissipationFromEnergy
#check @inducedAmplitude
#check @physical_production_from_strain_sup
#check @shell_vorticity_energy_bound
#check @physical_production_closure_inst

end NSFourier
