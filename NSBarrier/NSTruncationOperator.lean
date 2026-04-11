import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSUniform
import NSBarrier.NSTruncationConsistency
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSTruncationConsistency

namespace NSTruncationOperator

-- ============================================================
-- SECTION 1: BASIC TRUNCATION OPERATORS
-- ============================================================

/-- Restrict an infinite shell function to truncation level `K_max`. -/
def restrictShell {K_max : ℕ} (F : ℕ → ℝ) : Fin K_max → ℝ :=
  fun k => F k.val

@[simp] theorem restrictShell_apply {K_max : ℕ} (F : ℕ → ℝ) (k : Fin K_max) :
    restrictShell F k = F k.val := rfl

@[simp] theorem restrictShell_succEmbed {K : ℕ} (F : ℕ → ℝ) (k : Fin K) :
    restrictShell (K_max := K + 1) F (succEmbed k) =
      restrictShell (K_max := K) F k := by
  rfl

#check @restrictShell
#check @restrictShell_apply
#check @restrictShell_succEmbed

-- ============================================================
-- SECTION 2: INFINITE SHELL DATA
-- ============================================================

/-- Infinite shell-budget data, indexed by time and shell number. -/
structure InfiniteShellBudget where
  P_inf : ℕ → ℕ → ℝ
  D_inf : ℕ → ℕ → ℝ
  D_inf_nonneg : ∀ n k, 0 ≤ D_inf n k

/-- Infinite Fourier-side data, indexed by time and shell number. -/
structure InfiniteFourierData where
  shellEnergy_inf : ℕ → ℕ → ℝ
  shellVorticitySq_inf : ℕ → ℕ → ℝ
  strainSup_inf : ℕ → ℝ
  shellEnergy_nonneg : ∀ n k, 0 ≤ shellEnergy_inf n k
  shellVorticitySq_nonneg : ∀ n k, 0 ≤ shellVorticitySq_inf n k
  strainSup_nonneg : ∀ n, 0 ≤ strainSup_inf n

#check @InfiniteShellBudget
#check @InfiniteFourierData

-- ============================================================
-- SECTION 3: INDUCED FINITE TRUNCATION FAMILIES
-- ============================================================

/-- The finite shell budget induced by truncating an infinite shell budget. -/
def inducedShellBudget
    (infB : InfiniteShellBudget) (K_max n : ℕ) : ShellBudget K_max where
  P := restrictShell (infB.P_inf n)
  D := restrictShell (infB.D_inf n)
  D_nonneg := by
    intro k
    exact infB.D_inf_nonneg n k.val

/-- The induced budget-trajectory family. -/
def inducedBudgetTrajectoryFamily
    (infB : InfiniteShellBudget) : BudgetTrajectoryFamily :=
  fun K_max n => inducedShellBudget infB K_max n

/-- The finite Fourier state induced by truncating infinite Fourier data. -/
def inducedFourierState
    (infF : InfiniteFourierData) (K_max n : ℕ) : FourierState K_max where
  shellEnergy := restrictShell (infF.shellEnergy_inf n)
  shellVorticitySq := restrictShell (infF.shellVorticitySq_inf n)
  strainSup := infF.strainSup_inf n

/-- The induced Fourier-trajectory family. -/
def inducedFourierTrajectoryFamily
    (infF : InfiniteFourierData) : FourierTrajectoryFamily :=
  fun K_max n => inducedFourierState infF K_max n

@[simp] theorem inducedShellBudget_P
    (infB : InfiniteShellBudget) (K_max n : ℕ) (k : Fin K_max) :
    (inducedShellBudget infB K_max n).P k = infB.P_inf n k.val := rfl

@[simp] theorem inducedShellBudget_D
    (infB : InfiniteShellBudget) (K_max n : ℕ) (k : Fin K_max) :
    (inducedShellBudget infB K_max n).D k = infB.D_inf n k.val := rfl

@[simp] theorem inducedFourierState_shellEnergy
    (infF : InfiniteFourierData) (K_max n : ℕ) (k : Fin K_max) :
    (inducedFourierState infF K_max n).shellEnergy k = infF.shellEnergy_inf n k.val := rfl

@[simp] theorem inducedFourierState_shellVorticitySq
    (infF : InfiniteFourierData) (K_max n : ℕ) (k : Fin K_max) :
    (inducedFourierState infF K_max n).shellVorticitySq k = infF.shellVorticitySq_inf n k.val := rfl

@[simp] theorem inducedFourierState_strainSup
    (infF : InfiniteFourierData) (K_max n : ℕ) :
    (inducedFourierState infF K_max n).strainSup = infF.strainSup_inf n := rfl

#check @inducedShellBudget
#check @inducedBudgetTrajectoryFamily
#check @inducedFourierState
#check @inducedFourierTrajectoryFamily

-- ============================================================
-- SECTION 4: TRUNCATION CONSISTENCY
-- ============================================================

/-- The induced family preserves shell data across one-step truncation. -/
theorem shellDataPreservedStep_of_induced
    (infB : InfiniteShellBudget) :
    ShellDataPreservedStep (inducedBudgetTrajectoryFamily infB) := by
  intro K n k
  constructor <;>
    simp [inducedBudgetTrajectoryFamily, inducedShellBudget, restrictShell]

/-- Hence the induced family is truncation-consistent. -/
theorem consistentTruncation_of_induced
    (infB : InfiniteShellBudget) :
    ConsistentTruncation (inducedBudgetTrajectoryFamily infB) := by
  exact
    consistentTruncation_of_preserved_step
      (inducedBudgetTrajectoryFamily infB)
      (shellDataPreservedStep_of_induced infB)

#check @shellDataPreservedStep_of_induced
#check @consistentTruncation_of_induced

-- ============================================================
-- SECTION 5: POINTWISE INFINITE HYPOTHESES
-- ============================================================

/-- Infinite shellwise production-from-strain-sup hypothesis. -/
def InfiniteProductionFromStrainSup
    (infB : InfiniteShellBudget)
    (infF : InfiniteFourierData) : Prop :=
  ∀ n k, infB.P_inf n k ≤ infF.strainSup_inf n * infF.shellVorticitySq_inf n k

/-- Infinite shellwise vorticity-energy bound. -/
def InfiniteShellVorticityEnergyBound
    (infF : InfiniteFourierData)
    (C_shell : ℝ) : Prop :=
  ∀ (n k : ℕ), infF.shellVorticitySq_inf n k ≤ C_shell * (k : ℝ) ^ 2 * infF.shellEnergy_inf n k

/-- Infinite shellwise dissipation-from-energy bound. -/
def InfiniteDissipationFromEnergy
    (infB : InfiniteShellBudget)
    (infF : InfiniteFourierData)
    (ν : ℝ) : Prop :=
  ∀ (n k : ℕ), ν * (k : ℝ) ^ 4 * infF.shellEnergy_inf n k ≤ infB.D_inf n k

#check @InfiniteProductionFromStrainSup
#check @InfiniteShellVorticityEnergyBound
#check @InfiniteDissipationFromEnergy

-- ============================================================
-- SECTION 6: INFINITE -> UNIFORM BRIDGES
-- ============================================================

/-- The induced Fourier family has uniformly nonnegative strain-sup. -/
theorem uniformStrainSupNonneg_of_induced
    (infF : InfiniteFourierData) :
    UniformStrainSupNonneg (inducedFourierTrajectoryFamily infF) := by
  intro K_max n
  simp only [inducedFourierTrajectoryFamily, inducedFourierState]
  exact infF.strainSup_nonneg n

/-- The induced Fourier family has uniformly nonnegative shell energy. -/
theorem uniformShellEnergyNonneg_of_induced
    (infF : InfiniteFourierData) :
    UniformShellEnergyNonneg (inducedFourierTrajectoryFamily infF) := by
  intro K_max n k
  simp only [inducedFourierTrajectoryFamily, inducedFourierState]
  exact infF.shellEnergy_nonneg n k.val

/-- A pointwise infinite production-from-strain-sup bound induces
    the uniform finite-truncation production hypothesis. -/
theorem uniformProductionFromStrainSup_of_induced
    (infB : InfiniteShellBudget)
    (infF : InfiniteFourierData)
    (hprod : InfiniteProductionFromStrainSup infB infF) :
    UniformProductionFromStrainSup
      (inducedBudgetTrajectoryFamily infB)
      (inducedFourierTrajectoryFamily infF) := by
  refine ⟨0, ?_⟩
  intro K_max n _hn k
  simp only [inducedBudgetTrajectoryFamily, inducedShellBudget,
    inducedFourierTrajectoryFamily, inducedFourierState, restrictShell]
  exact hprod (n + 1) k.val

/-- A pointwise infinite shell-vorticity-energy bound induces
    the uniform finite-truncation shell-vorticity-energy bound. -/
theorem uniformShellVorticityEnergyBound_of_induced
    (infF : InfiniteFourierData)
    (C_shell : ℝ)
    (hXiE : InfiniteShellVorticityEnergyBound infF C_shell) :
    UniformShellVorticityEnergyBound
      (inducedFourierTrajectoryFamily infF)
      C_shell := by
  refine ⟨0, ?_⟩
  intro K_max n _hn k
  simp only [inducedFourierTrajectoryFamily, inducedFourierState, restrictShell]
  exact hXiE (n + 1) k.val

/-- A pointwise infinite dissipation-from-energy bound induces
    the uniform finite-truncation dissipation hypothesis. -/
theorem uniformDissipationFromEnergy_of_induced
    (infB : InfiniteShellBudget)
    (infF : InfiniteFourierData)
    (ν : ℝ)
    (hD : InfiniteDissipationFromEnergy infB infF ν) :
    UniformDissipationFromEnergy
      (inducedBudgetTrajectoryFamily infB)
      (inducedFourierTrajectoryFamily infF)
      ν := by
  refine ⟨0, ?_⟩
  intro K_max n _hn k
  simp only [inducedBudgetTrajectoryFamily, inducedShellBudget,
    inducedFourierTrajectoryFamily, inducedFourierState, restrictShell]
  exact hD (n + 1) k.val

#check @uniformStrainSupNonneg_of_induced
#check @uniformShellEnergyNonneg_of_induced
#check @uniformProductionFromStrainSup_of_induced
#check @uniformShellVorticityEnergyBound_of_induced
#check @uniformDissipationFromEnergy_of_induced

end NSTruncationOperator
