import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSBridge

/-!
# NSUniformBridge
Bridge layer from uniform-in-K_max Fourier hypotheses
to uniform / pointwise front stabilization statements.
-/

namespace NSUniformBridge

/-- From the uniform Fourier-side hypotheses, corridor advance is eventually impossible
    simultaneously for all truncation levels `K_max`. -/
theorem uniform_eventually_no_corridorStep_from_fourier_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∃ N : ℕ, ∀ K_max n, N ≤ n → ¬ corridorStep ((btraj K_max) n) ((btraj K_max) (n + 1)) := by
  rcases uniform_hypotheses_after_max btraj ftraj ν C_shell hA hP hX hD with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  have h_all := hN K_max n hn
  exact no_advance_from_fourier_inst
    ((btraj K_max) n)
    ((btraj K_max) (n + 1))
    (ftraj K_max (n + 1))
    ν C_shell
    h_all.1
    (hS K_max (n + 1))
    (hE K_max (n + 1))
    h_all.2.1
    h_all.2.2.1
    h_all.2.2.2

/-- Uniform Fourier-side hypotheses imply that the front is eventually
    nonincreasing simultaneously for all truncation levels. -/
theorem uniform_eventually_nonincreasing_front_from_fourier_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    UniformEventuallyNonincreasingFront btraj := by
  rcases uniform_eventually_no_corridorStep_from_fourier_inst
      btraj ftraj ν C_shell hS hE hA hP hX hD with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  have hnc : ¬ corridorStep ((btraj K_max) n) ((btraj K_max) (n + 1)) := hN K_max n hn
  exact Nat.not_lt.mp hnc

/-- For each fixed truncation level `K_max`, the uniform Fourier-side hypotheses
    imply eventual constancy of the front. The threshold time may be chosen
    uniformly, but the stabilized value may depend on `K_max`. -/
theorem pointwise_eventually_constant_from_uniform_fourier_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ m N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) = m := by
  rcases uniform_hypotheses_after_max btraj ftraj ν C_shell hA hP hX hD with
    ⟨N, hN⟩
  intro K_max
  have hA' :
      ∃ Na : ℕ, ∀ n : ℕ, Na ≤ n →
        inducedAmplitude (ftraj K_max (n + 1)) C_shell
          ≤ ν * (jumpFront ((btraj K_max) (n + 1)) : ℝ) ^ 2 := by
    refine ⟨N, ?_⟩
    intro n hn
    exact (hN K_max n hn).1
  have hP' :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n →
        ProductionFromStrainSup ((btraj K_max) (n + 1)).P (ftraj K_max (n + 1)) := by
    refine ⟨N, ?_⟩
    intro n hn
    exact (hN K_max n hn).2.1
  have hX' :
      ∃ Nx : ℕ, ∀ n : ℕ, Nx ≤ n →
        ShellVorticityEnergyBound (ftraj K_max (n + 1)) C_shell := by
    refine ⟨N, ?_⟩
    intro n hn
    exact (hN K_max n hn).2.2.1
  have hD' :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        DissipationFromEnergy ((btraj K_max) (n + 1)).D ν (ftraj K_max (n + 1)) := by
    refine ⟨N, ?_⟩
    intro n hn
    exact (hN K_max n hn).2.2.2
  exact jumpFront_eventually_constant_from_fourier_inst
    (btraj K_max)
    (ftraj K_max)
    ν C_shell
    (fun n => hS K_max n)
    (fun n => hE K_max n)
    hA' hP' hX' hD'

/-- Pointwise eventual constancy yields pointwise eventual boundedness
    for each truncation level. -/
theorem pointwise_eventually_bounded_from_uniform_fourier_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (hX : UniformShellVorticityEnergyBound ftraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  intro K_max
  rcases pointwise_eventually_constant_from_uniform_fourier_inst
      btraj ftraj ν C_shell hS hE hA hP hX hD K_max with
    ⟨m, N, hN⟩
  exact ⟨m, N, fun n hn => by rw [hN n hn]⟩

#check @uniform_eventually_no_corridorStep_from_fourier_inst
#check @uniform_eventually_nonincreasing_front_from_fourier_inst
#check @pointwise_eventually_constant_from_uniform_fourier_inst
#check @pointwise_eventually_bounded_from_uniform_fourier_inst

end NSUniformBridge
