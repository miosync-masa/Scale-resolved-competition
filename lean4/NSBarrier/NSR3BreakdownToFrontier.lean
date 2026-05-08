import NSBarrier.NSMillenniumFrontier
import NSBarrier.NSR3CounterexampleData
import Mathlib.Tactic

namespace NSR3BreakdownToFrontier

open NSMillenniumFrontier
open NSR3BreakdownDefinition
open NSR3CounterexampleData
open NSR3SolutionPackage

/-- Data for the E5 bridge from an Euclidean breakdown witness to failure of
any frontier hypothesis that would force a finite-step Gronwall bound for the
same enstrophy trajectory. -/
structure R3BreakdownFrontierData (K_max : ℕ) where
  counterexampleData : R3SmoothCounterexampleData K_max
  M : ℝ
  C : ℝ
  E0 : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hE0 : 0 ≤ E0
  hgronwall_from_frontier :
    ∀ _hyp : MillenniumFrontierHypothesis,
      ∀ n : ℕ,
        r3EnstrophyTrajectory counterexampleData.witness.pkg n
          ≤
        (1 + M * C) ^ n * E0

/-- E5 bridge theorem: once an Euclidean discrete breakdown witness exists, any
frontier hypothesis that would enforce the corresponding finite-step Gronwall
bound is impossible. -/
theorem R3_breakdown_implies_frontier_failure
    {K_max : ℕ}
    (d : R3BreakdownFrontierData K_max) :
    MillenniumFrontierHypothesis → False := by
  intro hyp
  exact
    blowup_at_fixed_step_implies_contradiction
      d.M d.C d.E0 d.hM d.hMC d.hE0
      (r3EnstrophyTrajectory d.counterexampleData.witness.pkg)
      d.counterexampleData.witness.nstar
      (d.hgronwall_from_frontier hyp d.counterexampleData.witness.nstar)
      d.counterexampleData.witness.hblowup

end NSR3BreakdownToFrontier
