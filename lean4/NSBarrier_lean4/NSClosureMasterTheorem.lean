import NSBarrier.NSLowShellLocalClosureActual
import NSBarrier.NSFiniteBandEnergy
import NSBarrier.NSFiniteFourierBernstein
import NSBarrier.NSLocalH1EnergyBound
import Mathlib.Tactic

/-!
# Closure Master Theorem

**Theorem I** of the paper.

Given:
- [Geom] Actual unit-width Euclidean triad geometry with offset C0 = 2
- [Alg]  Finite-band Cauchy-Schwarz (Bernstein constant)
- [Alg]  Low-shell H1 energy bound
- [Alg]  Shell decomposition P = P_loc + P_tail
- [Alg]  Eventual tail dissipation

Then the enstrophy trajectory satisfies a conditional discrete
Gronwall bound with explicit constants.

No structure fields appear in the statement.
All intermediate hypotheses are discharged in the proof.
-/

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandEnergy
open NSLowShellLocalClosureActual
open NSFiniteFourierBernstein
open NSLocalH1EnergyBound

namespace NSClosureMasterTheorem

/-- **Closure Master Theorem.**

If the shell budget trajectory admits:
1. a triad-support decomposition with actual Euclidean geometry,
2. eventual tail dissipation above the cutoff,
3. low-shell dissipation controlled by the enstrophy,
4. total shell energy eventually bounded,

then the enstrophy trajectory is eventually exponentially bounded:

    E(N0 + m) ≤ (1 + M * C)^m * E(N0)

where M depends on the Bernstein constant, the cutoff, and nu. -/
theorem finite_band_barrier_closure_master
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (supportData : ActualUnitWidthSupportExclusionData K_max)
    (F : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n
        ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ, ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, supportData.Ncut ≤ k.val →
          (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k =
          supportData.split.P_loc n k
            + supportData.split.P_tail n k)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < supportData.Ncut →
          supportData.split.P_loc n k
            ≤ F (lowShellEnergy Eshell supportData.Ncut n)
              * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (traj n)
          (lowShells (K_max := K_max) supportData.Ncut)
          ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n →
          totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ m : ℕ,
        E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 :=
  eventual_discrete_gronwall_of_actual_unitWidth_geometry
    traj E Eshell supportData F C
    hC hFmono hFnonneg hEn
    hinc htail hdecomp hloc hDiss hEtot

#check @finite_band_barrier_closure_master

end NSClosureMasterTheorem
