import NSBarrier.NSGalerkinShellStepIdentity
import NSBarrier.NSR3LocalWellposedness
import NSBarrier.NSR3NavierStokesActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSGalerkinExistenceTheorems
open NSGalerkinShellStepIdentity

namespace NSR3SolutionPackage

open NSFiniteSource
open NSFourier
open NSR3ActualTrueFields
open NSR3LocalWellposedness
open NSR3MinimalPDEFrontier
open NSR3ShellActual

/-- Euclidean actual solution package, parallel to the torus-side one.

This keeps together:
1. a local Picard-Lindelöf seed package on some finite-dimensional Galerkin system;
2. a genuine `R³` actual true-field slice;
3. a shellwise Galerkin enstrophy trajectory.

The identification between the local seed and the actual true-field slice is
recorded only at the level of the initial vorticity field. -/
structure R3ActualSolutionPackage (K_max : ℕ) where
  trueData : R3NavierStokesTrueFieldData K_max
  localData : Σ m : ℕ, R3LocalWellposednessData m
  shellStepData : GalerkinShellStepIdentityData K_max
  hinitial :
    (toPrimitiveR3StrainRegularityData_of_true_fields_R3 trueData).vorticity =
      localData.2.vorticity

/-- The primitive Euclidean PDE-facing package carried by an actual solution
package. -/
noncomputable def R3ActualSolutionPackage.pdeData
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    PrimitiveR3StrainRegularityData K_max :=
  toPrimitiveR3StrainRegularityData_of_true_fields_R3 pkg.trueData

/-- The discrete enstrophy trajectory associated with the shellwise Galerkin
data in the Euclidean solution package. -/
noncomputable def r3EnstrophyTrajectory
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :=
  shellTotalEnstrophy pkg.shellStepData.Xi

/-- The Euclidean solution package carries the same local existence seed as its
local wellposedness component. -/
noncomputable def localExistenceSeed_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    LocalExistenceSeed pkg.localData.1 pkg.localData.2.spec :=
  localExistenceSeed_of_R3_local_wellposedness pkg.localData.2

/-- The local Euclidean initial datum still supplies the `L²(R³)` frontier
input after packaging, hence so does the PDE-facing initial vorticity by the
bookkeeping equality `hinitial`. -/
theorem initial_vorticity_mem_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    MemLp pkg.pdeData.vorticity (2 : ℝ≥0∞) NSR3ShellActual.μR3 := by
  simpa [R3ActualSolutionPackage.pdeData, pkg.hinitial] using
    initial_vorticity_mem_of_R3_local_wellposedness pkg.localData.2

/-- The true-field component of the Euclidean package instantiates the minimal
PDE frontier unchanged. -/
theorem true_fields_imply_minimal_pde_frontier_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    (∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 pkg.pdeData.Sop k) ⊤ μR3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (pkg.pdeData.Sop k x) (pkg.pdeData.shellOmega k x))
        (2 : ℝ≥0∞) μR3) := by
  simpa [R3ActualSolutionPackage.pdeData] using
    true_fields_imply_minimal_pde_frontier_R3_actual pkg.trueData

/-- The actual true-field component also yields the abstract
`ProductionFromStrainSup` needed downstream. -/
theorem productionFromStrainSup_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    ProductionFromStrainSup
      (NSAnalyticA1Locality.localizedProduction
        (NSStrainAction.localizedData
          (NSR3NavierStokesActual.toR3ShellStrainActionData pkg.trueData)))
      (NSStrainAction.strainState
        (NSR3NavierStokesActual.toR3ShellStrainActionData pkg.trueData)) := by
  simpa using
    NSR3NavierStokesActual.productionFromStrainSup_of_R3_true_fields pkg.trueData

/-- The shellwise Galerkin identity yields the exact one-step enstrophy
identity for the packaged Euclidean trajectory. -/
theorem enstrophy_step_identity_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    ∀ n : ℕ,
      r3EnstrophyTrajectory pkg (n + 1) - r3EnstrophyTrajectory pkg n
        =
      shellNetSource (pkg.shellStepData.budgetData.intTraj n) Finset.univ := by
  intro n
  exact step_total_eq pkg.shellStepData n

/-- The shellwise Galerkin data also produce the standard enstrophy-identity
package used by later discrete Grönwall layers. -/
noncomputable def toGalerkinEnstrophyIdentityData_of_actual_solution_package_R3
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    NSGalerkinEnstrophyIdentity.GalerkinEnstrophyIdentityData K_max :=
  toGalerkinEnstrophyIdentityData pkg.shellStepData

/-- Final `R³` wrapper: an actual Euclidean solution package simultaneously
provides

1. a local existence seed,
2. the `L²(R³)` vorticity input,
3. the instantiated minimal PDE frontier,
4. the exact discrete enstrophy trajectory. -/
theorem R3_actual_solution_package_with_enstrophy_trajectory
    {K_max : ℕ}
    (pkg : R3ActualSolutionPackage K_max) :
    ∃ seed : LocalExistenceSeed pkg.localData.1 pkg.localData.2.spec,
      seed.T0 = pkg.localData.2.T0 ∧
      MemLp pkg.pdeData.vorticity (2 : ℝ≥0∞) μR3 ∧
      (∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 pkg.pdeData.Sop k) ⊤ μR3) ∧
      (∀ k : Fin K_max,
        MemLp (fun x => (pkg.pdeData.Sop k x) (pkg.pdeData.shellOmega k x))
          (2 : ℝ≥0∞) μR3) ∧
      (∀ n : ℕ,
        r3EnstrophyTrajectory pkg (n + 1) - r3EnstrophyTrajectory pkg n
          =
        shellNetSource (pkg.shellStepData.budgetData.intTraj n) Finset.univ) := by
  refine ⟨localExistenceSeed_of_actual_solution_package_R3 pkg, rfl, ?_⟩
  refine ⟨initial_vorticity_mem_of_actual_solution_package_R3 pkg, ?_⟩
  refine ⟨(true_fields_imply_minimal_pde_frontier_of_actual_solution_package_R3 pkg).1, ?_⟩
  refine ⟨(true_fields_imply_minimal_pde_frontier_of_actual_solution_package_R3 pkg).2, ?_⟩
  exact enstrophy_step_identity_of_actual_solution_package_R3 pkg

end NSR3SolutionPackage
