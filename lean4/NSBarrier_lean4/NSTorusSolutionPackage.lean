import NSBarrier.NSTorusLocalWellposedness
import NSBarrier.NSTorusMinimalPDEFrontier
import NSBarrier.NSGalerkinShellStepIdentity
import NSBarrier.NSStrainOpVectorActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSActualSigmaBound
open NSTorusLocalWellposedness
open NSTorusMinimalPDEFrontier
open NSGalerkinExistenceTheorems
open NSGalerkinShellStepIdentity
open NSFiniteSource

namespace NSTorusSolutionPackage

/-- Torus-side package that keeps together the three ingredients needed by the current
paper-facing continuation chain:

1. a local Picard-Lindelöf seed;
2. a true-field / minimal-PDE frontier slice;
3. a shellwise Galerkin enstrophy trajectory.

At this stage we intentionally only bundle the data. The explicit identification between the
local torus solution, the true-field slice, and the Galerkin shell trajectory is deferred to the
next bridge layers. -/
structure TorusActualSolutionPackage (K_max m : ℕ)
    extends TorusTrueFieldMinimalPDEData K_max where
  localData : TorusLocalWellposednessData m
  shellStepData : GalerkinShellStepIdentityData K_max

/-- The discrete enstrophy trajectory associated with the shellwise Galerkin data in the torus
solution package. -/
noncomputable def torusEnstrophyTrajectory
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :=
  shellTotalEnstrophy pkg.shellStepData.Xi

/-- The torus solution package carries the same local existence seed as its local wellposedness
component. -/
noncomputable def localExistenceSeed_of_actual_solution_package_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    LocalExistenceSeed m pkg.localData.spec :=
  localExistenceSeed_of_torus_local_wellposedness pkg.localData

/-- The local torus initial datum still supplies the `L²(T³)` frontier input after packaging. -/
theorem initial_vorticity_mem_of_actual_solution_package_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    MemLp pkg.localData.initialData.vorticity (2 : ℝ≥0∞) μT3 :=
  initial_vorticity_mem_of_torus_local_wellposedness pkg.localData

/-- The true-field component of the package instantiates the minimal PDE frontier unchanged. -/
theorem true_fields_imply_minimal_pde_frontier_of_actual_solution_package_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    (∀ k : Fin K_max, MemLp (sigmaFromOpNorm pkg.Sop k) ⊤ μT3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (pkg.Sop k x) (pkg.shellOmega k x)) (2 : ℝ≥0∞) μT3) :=
  true_fields_imply_minimal_pde_frontier_T3 pkg.toTorusTrueFieldMinimalPDEData

/-- The shellwise Galerkin identity yields the exact one-step enstrophy identity for the packaged
trajectory. -/
theorem enstrophy_step_identity_of_actual_solution_package_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    ∀ n : ℕ,
      torusEnstrophyTrajectory pkg (n + 1) - torusEnstrophyTrajectory pkg n
        =
      shellNetSource (pkg.shellStepData.budgetData.intTraj n) Finset.univ := by
  intro n
  exact step_total_eq pkg.shellStepData n

/-- The shellwise Galerkin data also produce the standard enstrophy-identity package used by the
discrete Grönwall layers. -/
noncomputable def toGalerkinEnstrophyIdentityData_of_actual_solution_package_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    NSGalerkinEnstrophyIdentity.GalerkinEnstrophyIdentityData K_max :=
  toGalerkinEnstrophyIdentityData pkg.shellStepData

/-- Final T³ wrapper: an actual torus solution package simultaneously provides

1. the local existence seed,
2. the `L²(T³)` vorticity input,
3. the instantiated minimal PDE frontier,
4. the exact discrete enstrophy trajectory.

This is the hand-off point from the torus PDE-facing layers to the continuation and no-blowup
layers. -/
theorem actual_solution_package_with_enstrophy_trajectory_T3
    {K_max m : ℕ}
    (pkg : TorusActualSolutionPackage K_max m) :
    ∃ seed : LocalExistenceSeed m pkg.localData.spec,
      seed.T0 = pkg.localData.T0 ∧
      MemLp pkg.localData.initialData.vorticity (2 : ℝ≥0∞) μT3 ∧
      (∀ k : Fin K_max, MemLp (sigmaFromOpNorm pkg.Sop k) ⊤ μT3) ∧
      (∀ k : Fin K_max,
        MemLp (fun x => (pkg.Sop k x) (pkg.shellOmega k x)) (2 : ℝ≥0∞) μT3) ∧
      (∀ n : ℕ,
        torusEnstrophyTrajectory pkg (n + 1) - torusEnstrophyTrajectory pkg n
          =
        shellNetSource (pkg.shellStepData.budgetData.intTraj n) Finset.univ) := by
  refine ⟨localExistenceSeed_of_actual_solution_package_T3 pkg, rfl, ?_⟩
  refine ⟨initial_vorticity_mem_of_actual_solution_package_T3 pkg, ?_⟩
  refine ⟨(true_fields_imply_minimal_pde_frontier_of_actual_solution_package_T3 pkg).1, ?_⟩
  refine ⟨(true_fields_imply_minimal_pde_frontier_of_actual_solution_package_T3 pkg).2, ?_⟩
  exact enstrophy_step_identity_of_actual_solution_package_T3 pkg

end NSTorusSolutionPackage
