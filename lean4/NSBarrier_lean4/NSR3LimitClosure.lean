import NSBarrier.NSR3SolutionPackage
import NSBarrier.NSCompactnessConvergenceActual
import NSBarrier.NSLimitClosureStability
import Mathlib.Tactic

open Filter
open NSTorusShellActual

namespace NSR3LimitClosure

open NSCompactnessConvergenceActual
open NSGalerkinCompactnessActual
open NSLimitClosureStability
open NSWeakToStrongGap

/-- `R³`-side bundle connecting the actual Euclidean solution package to the
verified compactness / limit-closure chain.

As in the torus file, the remaining fields identify the abstract limit
trajectories `Elim`, `Dlim` with the concrete state-level coefficient formulas
used in `NSCompactnessConvergenceActual`. -/
structure R3LimitClosureData (K_max m : ℕ) where
  solutionPkg : NSR3SolutionPackage.R3ActualSolutionPackage K_max
  stateData : CompactnessConvergenceStateData K_max m
  compactnessData : GalerkinCompactnessData
  Ncut : ℕ
  M : ℝ
  C : ℝ
  hM : 0 ≤ M
  hMC : 0 ≤ M * C
  hstep_family : ∀ i : ℕ, ∀ n : ℕ,
    compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + (n + 1))
      - compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + n)
      ≤ M * C * compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + n)
  hDlow_le_CE : ∀ i : ℕ, ∀ n : ℕ,
    compactnessData.Dlow i
        (compactnessData.gronwallData.N0 + n)
      ≤ C * compactnessData.gronwallData.E i
        (compactnessData.gronwallData.N0 + n)
  hN0_match : compactnessData.gronwallData.N0 = stateData.N0
  hsubseq_match : compactnessData.subseq = stateData.subseq
  hElim_model :
    ∀ n : ℕ,
      (∑ k : Fin K_max,
        NSGalerkinCoeffODEProductRuleProof.XiContOfCoeffs
          stateData.modes stateData.shellOf stateData.weight
          (coeffOfStateLim stateData)
          (stateData.time n) k)
        =
      compactnessData.Elim (stateData.N0 + n)
  hE_model :
    ∀ j n : ℕ,
      (∑ k : Fin K_max,
        NSGalerkinCoeffODEProductRuleProof.XiContOfCoeffs
          stateData.modes stateData.shellOf stateData.weight
          (coeffOfStateFam stateData (stateData.subseq j))
          (stateData.time n) k)
        =
      compactnessData.gronwallData.E
        (stateData.subseq j) (stateData.N0 + n)
  hDlim_model :
    ∀ n : ℕ,
      (∑ k ∈ NSFiniteSourceTrajectory.lowShells (K_max := K_max) Ncut,
        NSGalerkinCoeffODEProductRuleProof.DContOfCoeffs
          stateData.modes stateData.shellOf stateData.weight
          (coeffOfStateLim stateData)
          stateData.damp (stateData.time n) k)
        =
      compactnessData.Dlim (stateData.N0 + n)
  hDlow_model :
    ∀ j n : ℕ,
      (∑ k ∈ NSFiniteSourceTrajectory.lowShells (K_max := K_max) Ncut,
        NSGalerkinCoeffODEProductRuleProof.DContOfCoeffs
          stateData.modes stateData.shellOf stateData.weight
          (coeffOfStateFam stateData (stateData.subseq j))
          stateData.damp (stateData.time n) k)
        =
      compactnessData.Dlow
        (stateData.subseq j) (stateData.N0 + n)

/-- The concrete state-level compactness data yield pointwise convergence of the
extracted Euclidean enstrophy trajectory appearing in the abstract
limit-closure package. -/
theorem hElim_tendsto_of_R3_limit_data
    {K_max m : ℕ}
    (d : R3LimitClosureData K_max m) :
    ∀ n : ℕ,
      Tendsto
        (fun j : ℕ =>
          d.compactnessData.gronwallData.E
            (d.compactnessData.subseq j)
            (d.compactnessData.gronwallData.N0 + n))
        atTop
        (nhds (d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + n))) := by
  intro n
  simpa [d.hsubseq_match, d.hN0_match, d.hE_model, d.hElim_model] using
    hElim_tendsto_of_state_compactness d.stateData n

/-- Likewise, the concrete state-level compactness data yield pointwise
convergence of the low-shell dissipation trajectory used in the Euclidean
limit-closure package. -/
theorem hDlim_tendsto_of_R3_limit_data
    {K_max m : ℕ}
    (d : R3LimitClosureData K_max m) :
    ∀ n : ℕ,
      Tendsto
        (fun j : ℕ =>
          d.compactnessData.Dlow
            (d.compactnessData.subseq j)
            (d.compactnessData.gronwallData.N0 + n))
        atTop
        (nhds (d.compactnessData.Dlim
          (d.compactnessData.gronwallData.N0 + n))) := by
  intro n
  simpa [d.hsubseq_match, d.hN0_match, d.hDlow_model, d.hDlim_model] using
    hDlim_tendsto_of_state_compactness d.stateData d.Ncut n

/-- The `R³`-side compactness package induces the abstract
limit-closure stability data. -/
noncomputable def toLimitClosureStabilityData_of_R3
    {K_max m : ℕ}
    (d : R3LimitClosureData K_max m) :
    LimitClosureStabilityData where
  compactnessData := d.compactnessData
  M := d.M
  C := d.C
  hM := d.hM
  hMC := d.hMC
  hstep_family := d.hstep_family
  hElim_tendsto := hElim_tendsto_of_R3_limit_data d
  hDlim_tendsto := hDlim_tendsto_of_R3_limit_data d
  hDlow_le_CE := d.hDlow_le_CE

/-- A3 wrapper theorem: once the `R³` compactness data are identified with the
abstract limit-side objects, the extracted Euclidean limit inherits the same
discrete closure / Gronwall law as the Galerkin family. -/
theorem R3_limit_solution_inherits_closure
    {K_max m : ℕ}
    (d : R3LimitClosureData K_max m) :
    ∀ n : ℕ,
      d.compactnessData.Elim
          (d.compactnessData.gronwallData.N0 + n)
        ≤
      (1 + d.M * d.C) ^ n
        * d.compactnessData.Elim
            d.compactnessData.gronwallData.N0 :=
  limit_closure_stability_master
    (toLimitClosureStabilityData_of_R3 d)

end NSR3LimitClosure
