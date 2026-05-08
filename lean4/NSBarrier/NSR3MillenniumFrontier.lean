import NSBarrier.NSMillenniumFrontier
import NSBarrier.NSR3UniformF
import Mathlib.Tactic

namespace NSR3MillenniumFrontier

open NSMillenniumFrontier
open NSR3UniformF

/-- The concrete Euclidean finite-band closure function from the verified `R³`
Bernstein chain instantiates the abstract millennium frontier hypothesis. -/
noncomputable def millennium_frontier_hypothesis_of_R3_uniformF
    (Ncut : ℕ) :
    MillenniumFrontierHypothesis where
  F := r3UniformF Ncut
  hF_nonneg := r3UniformF_nonneg Ncut
  hF_mono := r3UniformF_mono Ncut
  hF_Kmax_independent := trivial

end NSR3MillenniumFrontier
