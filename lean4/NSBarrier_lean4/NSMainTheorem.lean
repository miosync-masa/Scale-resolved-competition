import NSBarrier.NSClosureMasterTheorem
import NSBarrier.NSRealizationMasterTheorem
import NSBarrier.NSGalerkinShellStepIdentity
import Mathlib.Tactic

/-!
# Main Theorem

Composition of Theorems I and II:

    minimal PDE / Galerkin assumptions ⟹ conditional global control

This is the single theorem to cite in the paper abstract.

The reader sees only:
1. Galerkin shellwise identity data
2. Tail dissipation, low-shell ratio bound, low-shell dissipation control
3. Final consequence: exponential enstrophy bound

All intermediate layers are consumed inside the proof.
-/

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandEnergy
open NSLowShellLocalClosureActual
open NSGalerkinShellStepIdentity

namespace NSMainTheorem

/-- **Main Theorem: Conditional Global Enstrophy Control.**

From the Galerkin shellwise exact identity, eventual tail
dissipation, low-shell ratio bound, and low-shell dissipation
control, the shellwise enstrophy trajectory is eventually
exponentially bounded:

    E(N0 + m) ≤ (1 + M * C)^m * E(N0)

This is Theorem I (Closure) composed with Theorem II (Realization)
into a single statement. -/
theorem conditional_global_control_from_ns_main
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ, ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, Ncut ≤ k.val →
          (gid.budgetData.instTraj n).P k
            ≤ (gid.budgetData.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ, ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (gid.budgetData.instTraj n).P k
            ≤ M * (gid.budgetData.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource
          (gid.budgetData.intTraj n)
          (lowShells (K_max := K_max) Ncut)
          ≤ C * shellTotalEnstrophy gid.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy gid.Xi (N0 + m)
          ≤ (1 + M * C) ^ m
            * shellTotalEnstrophy gid.Xi N0 :=
  eventual_discrete_gronwall_of_shellwise_step_identity_cutoff
    gid M C Ncut hM hMC htail hratio hDiss_gal

#check @conditional_global_control_from_ns_main

/-- **Barrier-Specialized Main Theorem.**

The same result under the K⁴ barrier hypothesis:
if the barrier eventually enforces tail dissipation,
and the low-shell ratio bound and dissipation control hold,
then the enstrophy is eventually exponentially bounded. -/
theorem conditional_global_control_barrier_main
    {K_max : ℕ}
    (gid : GalerkinShellStepIdentityData K_max)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ, ∀ n : ℕ, Nb ≤ n →
        ∀ k : Fin K_max,
          (gid.budgetData.instTraj n).D k
            < (gid.budgetData.instTraj n).P k →
          Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ, ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, Ncut ≤ k.val →
          (gid.budgetData.instTraj n).P k
            ≤ (gid.budgetData.instTraj n).D k)
    (hratio :
      ∃ Nr : ℕ, ∀ n : ℕ, Nr ≤ n →
        ∀ k : Fin K_max, k.val < Ncut →
          (gid.budgetData.instTraj n).P k
            ≤ M * (gid.budgetData.instTraj n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource
          (gid.budgetData.intTraj n)
          (lowShells (K_max := K_max) Ncut)
          ≤ C * shellTotalEnstrophy gid.Xi n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy gid.Xi (N0 + m)
          ≤ (1 + M * C) ^ m
            * shellTotalEnstrophy gid.Xi N0 :=
  eventual_discrete_gronwall_of_shellwise_step_identity_barrier_fixed_cutoff
    gid Φ ν M C Ncut hν hM hMC hbar htail hratio hDiss_gal

#check @conditional_global_control_barrier_main

end NSMainTheorem
