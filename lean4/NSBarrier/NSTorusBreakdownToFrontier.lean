import NSBarrier.NSMillenniumFrontier
import NSBarrier.NSTorusCounterexampleData
import Mathlib.Tactic

namespace NSTorusBreakdownToFrontier

open NSMillenniumFrontier
open NSTorusBreakdownDefinition
open NSTorusCounterexampleData
open NSTorusSolutionPackage

/-- Data for the D3 bridge from a torus-side breakdown witness to failure of any
frontier hypothesis that would force a finite-step Grönwall bound for the same
enstrophy trajectory. -/
structure TorusBreakdownFrontierData (K_max m : ℕ) where
  counterexampleData : TorusSmoothCounterexampleData K_max m
  M : ℝ
  C : ℝ
  E0 : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hE0 : 0 ≤ E0
  hgronwall_from_frontier :
    ∀ hyp : MillenniumFrontierHypothesis,
      ∀ n : ℕ,
        torusEnstrophyTrajectory counterexampleData.witness.pkg n
          ≤
        (1 + M * C) ^ n * E0

/-- D3 bridge theorem: once a torus-side discrete breakdown witness exists, any
frontier hypothesis that would enforce the corresponding finite-step Grönwall
bound is impossible. -/
theorem torus_breakdown_implies_frontier_failure
    {K_max m : ℕ}
    (d : TorusBreakdownFrontierData K_max m) :
    MillenniumFrontierHypothesis → False := by
  intro hyp
  exact
    blowup_at_fixed_step_implies_contradiction
      d.M d.C d.E0 d.hM d.hMC d.hE0
      (torusEnstrophyTrajectory d.counterexampleData.witness.pkg)
      d.counterexampleData.witness.nstar
      (d.hgronwall_from_frontier hyp d.counterexampleData.witness.nstar)
      d.counterexampleData.witness.hblowup

end NSTorusBreakdownToFrontier
