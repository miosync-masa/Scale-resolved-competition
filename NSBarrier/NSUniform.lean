import NSBarrier.Basic
import NSBarrier.NSFourier
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier

/-!
# NSUniform
Uniform-in-K_max interface for shellwise Navier–Stokes barrier arguments.

This file packages the hypotheses needed to pass from finite shell models
toward truncation-independent / uniform statements.
-/

namespace NSUniform

-- ============================================================
-- SECTION 1: FAMILIES
-- ============================================================

/-- A family of budget trajectories indexed by the shell cutoff `K_max`. -/
def BudgetTrajectoryFamily := ∀ K_max : ℕ, BudgetTrajectory K_max

/-- A family of Fourier trajectories indexed by the shell cutoff `K_max`. -/
def FourierTrajectoryFamily := ∀ K_max : ℕ, ℕ → FourierState K_max

-- ============================================================
-- SECTION 2: UNIFORM HYPOTHESES
-- ============================================================

/-- Uniform nonnegativity of strain-sup along a Fourier trajectory family. -/
def UniformStrainSupNonneg
    (ftraj : FourierTrajectoryFamily) : Prop :=
  ∀ K_max n, 0 ≤ (ftraj K_max n).strainSup

/-- Uniform nonnegativity of shell energy along a Fourier trajectory family. -/
def UniformShellEnergyNonneg
    (ftraj : FourierTrajectoryFamily) : Prop :=
  ∀ K_max n, ShellEnergyNonneg (ftraj K_max n)

/-- Uniform barrier threshold:
    after a common time `N`, the induced amplitude is below the front k²-threshold
    for every truncation level `K_max`. -/
def UniformBarrierThreshold
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    inducedAmplitude (ftraj K_max (n + 1)) C_shell
      ≤ ν * (jumpFront ((btraj K_max) (n + 1)) : ℝ) ^ 2

/-- Uniform shellwise production-from-strain-sup hypothesis. -/
def UniformProductionFromStrainSup
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    ProductionFromStrainSup ((btraj K_max) (n + 1)).P (ftraj K_max (n + 1))

/-- Uniform shellwise vorticity-energy bound. -/
def UniformShellVorticityEnergyBound
    (ftraj : FourierTrajectoryFamily)
    (C_shell : ℝ) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    ShellVorticityEnergyBound (ftraj K_max (n + 1)) C_shell

/-- Uniform shellwise dissipation-from-energy lower bound. -/
def UniformDissipationFromEnergy
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    DissipationFromEnergy ((btraj K_max) (n + 1)).D ν (ftraj K_max (n + 1))

-- ============================================================
-- SECTION 3: UNIFORM FRONT PROPERTIES
-- ============================================================

/-- The front is eventually uniformly nonincreasing across all truncation levels. -/
def UniformEventuallyNonincreasingFront
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    jumpFront ((btraj K_max) (n + 1)) ≤ jumpFront ((btraj K_max) n)

/-- The front is eventually uniformly bounded across all truncation levels. -/
def UniformEventuallyBoundedFront
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∃ M N : ℕ, ∀ K_max n, N ≤ n →
    jumpFront ((btraj K_max) n) ≤ M

/-- The front is eventually constant with a single common value across all truncation levels. -/
def UniformEventuallyConstantFront
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∃ m N : ℕ, ∀ K_max n, N ≤ n →
    jumpFront ((btraj K_max) n) = m

/-- Truncation consistency: increasing `K_max` does not decrease the front. -/
def ConsistentTruncation
    (btraj : BudgetTrajectoryFamily) : Prop :=
  ∀ K_max n, jumpFront ((btraj K_max) n) ≤ jumpFront ((btraj (K_max + 1)) n)

-- ============================================================
-- SECTION 4: COMBINING UNIFORM THRESHOLDS
-- ============================================================

/-- After the maximum of the individual threshold times, all uniform Fourier-side
    hypotheses hold simultaneously. -/
theorem uniform_hypotheses_after_max
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∃ N : ℕ, ∀ K_max n, N ≤ n →
      inducedAmplitude (ftraj K_max (n + 1)) C_shell
        ≤ ν * (jumpFront ((btraj K_max) (n + 1)) : ℝ) ^ 2
      ∧ ProductionFromStrainSup ((btraj K_max) (n + 1)).P (ftraj K_max (n + 1))
      ∧ ShellVorticityEnergyBound (ftraj K_max (n + 1)) C_shell
      ∧ DissipationFromEnergy ((btraj K_max) (n + 1)).D ν (ftraj K_max (n + 1)) := by
  rcases hA with ⟨Na, hA'⟩
  rcases hP with ⟨Np, hP'⟩
  rcases hX with ⟨Nx, hX'⟩
  rcases hD with ⟨Nd, hD'⟩
  refine ⟨max Na (max Np (max Nx Nd)), ?_⟩
  intro K_max n hn
  have hNa : Na ≤ n := by
    exact le_trans (le_max_left Na (max Np (max Nx Nd))) hn
  have hmid1 : max Np (max Nx Nd) ≤ n := by
    exact le_trans (le_max_right Na (max Np (max Nx Nd))) hn
  have hNp : Np ≤ n := by
    exact le_trans (le_max_left Np (max Nx Nd)) hmid1
  have hmid2 : max Nx Nd ≤ n := by
    exact le_trans (le_max_right Np (max Nx Nd)) hmid1
  have hNx : Nx ≤ n := by
    exact le_trans (le_max_left Nx Nd) hmid2
  have hNd : Nd ≤ n := by
    exact le_trans (le_max_right Nx Nd) hmid2
  exact ⟨hA' K_max n hNa, hP' K_max n hNp, hX' K_max n hNx, hD' K_max n hNd⟩

-- ============================================================
-- SECTION 5: BASIC CONSEQUENCES
-- ============================================================

/-- Uniform eventual constancy implies uniform eventual boundedness. -/
theorem uniform_eventual_bound_of_uniform_eventual_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    UniformEventuallyBoundedFront btraj := by
  rcases hconst with ⟨m, N, hN⟩
  refine ⟨m, N, ?_⟩
  intro K_max n hn
  rw [hN K_max n hn]

/-- Uniform eventual constancy gives a pointwise eventual bound for each truncation. -/
theorem pointwise_eventual_bound_of_uniform_eventual_constant
    (btraj : BudgetTrajectoryFamily)
    (hconst : UniformEventuallyConstantFront btraj) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  intro K_max
  rcases uniform_eventual_bound_of_uniform_eventual_constant btraj hconst with
    ⟨M, N, hN⟩
  exact ⟨M, N, fun n hn => hN K_max n hn⟩

/-- Uniform eventual boundedness gives a pointwise eventual bound for each truncation. -/
theorem pointwise_eventual_bound_of_uniform_eventual_bound
    (btraj : BudgetTrajectoryFamily)
    (hbound : UniformEventuallyBoundedFront btraj) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  intro K_max
  rcases hbound with ⟨M, N, hN⟩
  exact ⟨M, N, fun n hn => hN K_max n hn⟩

/-- A uniform bound immediately gives a truncation-independent front bound
    after the common threshold time. -/
theorem truncation_independent_bound_after_threshold
    (btraj : BudgetTrajectoryFamily)
    (hbound : UniformEventuallyBoundedFront btraj) :
    ∃ M N : ℕ, ∀ K_max n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  exact hbound

#check @BudgetTrajectoryFamily
#check @FourierTrajectoryFamily
#check @UniformStrainSupNonneg
#check @UniformShellEnergyNonneg
#check @UniformBarrierThreshold
#check @UniformProductionFromStrainSup
#check @UniformShellVorticityEnergyBound
#check @UniformDissipationFromEnergy
#check @UniformEventuallyNonincreasingFront
#check @UniformEventuallyBoundedFront
#check @UniformEventuallyConstantFront
#check @ConsistentTruncation
#check @uniform_hypotheses_after_max
#check @uniform_eventual_bound_of_uniform_eventual_constant
#check @pointwise_eventual_bound_of_uniform_eventual_constant
#check @pointwise_eventual_bound_of_uniform_eventual_bound
#check @truncation_independent_bound_after_threshold

end NSUniform
