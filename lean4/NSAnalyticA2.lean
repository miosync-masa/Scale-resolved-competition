import NSBarrier.NSFourier
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier

namespace NSAnalyticA2

-- ============================================================
-- SECTION 1: RADIUS-SQUARED CONTROL
-- ============================================================

/-- A shellwise radius-squared profile, intended to represent an upper bound
    for |κ|² on the shell indexed by k. -/
def RadiusSqProfile (K_max : ℕ) := Fin K_max → ℝ

/-- The zero shell carries no vorticity. This is the abstract replacement for the
    fact that the zero Fourier mode has zero curl. -/
def ZeroShellVorticity {K_max : ℕ} (fs : FourierState K_max) : Prop :=
  ∀ k : Fin K_max, k.val = 0 → fs.shellVorticitySq k = 0

/-- Shellwise vorticity is controlled by a shell radius-squared profile:
    Ξ_k ≤ R²_k · E_k. -/
def VorticityControlledByRadiusSq {K_max : ℕ}
    (fs : FourierState K_max)
    (R2 : RadiusSqProfile K_max) : Prop :=
  ∀ k : Fin K_max,
    fs.shellVorticitySq k ≤ R2 k * fs.shellEnergy k

/-- The shell radius-squared profile is controlled by the shell index:
    R²_k ≤ C_shell · k² for positive shells. -/
def RadiusSqControlledByIndex {K_max : ℕ}
    (R2 : RadiusSqProfile K_max)
    (C_shell : ℝ) : Prop :=
  ∀ k : Fin K_max, 0 < k.val → R2 k ≤ C_shell * (k.val : ℝ) ^ 2

/-- Main A2 reduction:
    zero-shell triviality + shell-energy nonnegativity + radius-squared control
    imply the shellwise vorticity-energy bound. -/
theorem shell_vorticity_energy_bound_from_radius
    {K_max : ℕ}
    (fs : FourierState K_max)
    (R2 : RadiusSqProfile K_max)
    (C_shell : ℝ)
    (h0 : ZeroShellVorticity fs)
    (hE : ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs R2)
    (hR : RadiusSqControlledByIndex R2 C_shell) :
    ShellVorticityEnergyBound fs C_shell := by
  intro k
  by_cases hk0 : k.val = 0
  · have hXi0 : fs.shellVorticitySq k = 0 := h0 k hk0
    simp [hk0, hXi0]
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    have hXi : fs.shellVorticitySq k ≤ R2 k * fs.shellEnergy k := hXiR k
    have hRk : R2 k ≤ C_shell * (k.val : ℝ) ^ 2 := hR k hkpos
    have hEk : 0 ≤ fs.shellEnergy k := hE k
    have hmul :
        R2 k * fs.shellEnergy k ≤
          (C_shell * (k.val : ℝ) ^ 2) * fs.shellEnergy k := by
      exact mul_le_mul_of_nonneg_right hRk hEk
    linarith

#check @RadiusSqProfile
#check @ZeroShellVorticity
#check @VorticityControlledByRadiusSq
#check @RadiusSqControlledByIndex
#check @shell_vorticity_energy_bound_from_radius

-- ============================================================
-- SECTION 2: UNIT-WIDTH SHELLS
-- ============================================================

/-- Radius-squared profile for unit-width spherical shells:
    R²_k = (k + 1/2)². -/
noncomputable def unitShellRadiusSq (K_max : ℕ) : RadiusSqProfile K_max :=
  fun k => ((k.val : ℝ) + (1 / 2 : ℝ)) ^ 2

/-- For positive shells, (k + 1/2)² ≤ (9/4) k². -/
theorem unitShellRadiusSq_control
    {K_max : ℕ} :
    RadiusSqControlledByIndex (unitShellRadiusSq K_max) (9 / 4 : ℝ) := by
  intro k hkpos
  unfold unitShellRadiusSq
  have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hkpos
  nlinarith

/-- A2 for unit-width spherical shells with the explicit constant 9/4. -/
theorem shell_vorticity_energy_bound_unit_shell
    {K_max : ℕ}
    (fs : FourierState K_max)
    (h0 : ZeroShellVorticity fs)
    (hE : ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs (unitShellRadiusSq K_max)) :
    ShellVorticityEnergyBound fs (9 / 4 : ℝ) := by
  exact
    shell_vorticity_energy_bound_from_radius
      fs
      (unitShellRadiusSq K_max)
      (9 / 4 : ℝ)
      h0
      hE
      hXiR
      unitShellRadiusSq_control

/-- Monotone corollary:
    any larger shell constant also works. -/
theorem shell_vorticity_energy_bound_unit_shell_of_le
    {K_max : ℕ}
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hC : (9 / 4 : ℝ) ≤ C_shell)
    (h0 : ZeroShellVorticity fs)
    (hE : ShellEnergyNonneg fs)
    (hXiR : VorticityControlledByRadiusSq fs (unitShellRadiusSq K_max)) :
    ShellVorticityEnergyBound fs C_shell := by
  intro k
  have h94 :
      fs.shellVorticitySq k ≤
        (9 / 4 : ℝ) * (k.val : ℝ) ^ 2 * fs.shellEnergy k :=
    shell_vorticity_energy_bound_unit_shell fs h0 hE hXiR k
  have hEk : 0 ≤ fs.shellEnergy k := hE k
  have hfac_nonneg : 0 ≤ (k.val : ℝ) ^ 2 * fs.shellEnergy k := by
    have hk2_nonneg : 0 ≤ (k.val : ℝ) ^ 2 := by positivity
    nlinarith
  have hmono :
      (9 / 4 : ℝ) * ((k.val : ℝ) ^ 2 * fs.shellEnergy k) ≤
        C_shell * ((k.val : ℝ) ^ 2 * fs.shellEnergy k) := by
    exact mul_le_mul_of_nonneg_right hC hfac_nonneg
  have hmono' :
      (9 / 4 : ℝ) * (k.val : ℝ) ^ 2 * fs.shellEnergy k ≤
        C_shell * (k.val : ℝ) ^ 2 * fs.shellEnergy k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmono
  linarith

#check @unitShellRadiusSq
#check @unitShellRadiusSq_control
#check @shell_vorticity_energy_bound_unit_shell
#check @shell_vorticity_energy_bound_unit_shell_of_le

end NSAnalyticA2
