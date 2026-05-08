import NSBarrier.NSActualSigmaBound
import NSBarrier.NSNavierStokesProjectedCore
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData)
open NSStrainOpVectorActual
open NSActualSigmaBound
open NSNavierStokesLpCore
open NSNavierStokesProjectedCore
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSActualSigmaStretch

/-- The final PDE-facing obligations, after all bookkeeping reductions.

At this stage, the only genuinely analytic inputs still needed from the true
Navier–Stokes fields are:

1. `sigma_mem` / `sigma_bound` for `σ = ‖Sop‖op`;
2. `stretch_dom`, i.e. the actual stretching output is `L²`-dominated by
   the scalar-amplified shell-projected vorticity field.

Everything else is already absorbed into the previous layers. -/
structure NavierStokesSigmaStretchData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  /-- Full vorticity field in `L²(T³; ℂ³)`. -/
  vorticityLp : L2VecT3

  /-- Pointwise strain operator field. -/
  Sop : Fin K_max → T3 → Mat3

  /-- Actual stretching output field in `L²(T³; ℂ³)`. -/
  stretchLp : Fin K_max → L2VecT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- `σ = ‖Sop‖op` belongs to `L∞(T³)`. -/
  sigma_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (sigmaFromOpNorm Sop k) ⊤ μT3

  /-- Its `L∞` norm is bounded by the shell-independent strain amplitude. -/
  sigma_bound :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (sigmaFromOpNorm Sop k) (sigma_mem k)‖ ≤ strainSup

  /-- The actual stretching output is dominated in `L²` by the scalar-amplified
      shell-projected vorticity field. -/
  stretch_dom :
    ∀ k : Fin K_max,
      ‖stretchLp k‖ ≤
        ‖(MeasureTheory.MemLp.toLp (sigmaFromOpNorm Sop k) (sigma_mem k)) •
          (projData.Pk k vorticityLp)‖

#check @NavierStokesSigmaStretchData

/-- Turn the final PDE-facing sigma/stretch data into the projected `Lp` core. -/
noncomputable def toProjectedLpCoreData
    {K_max : ℕ}
    (ns : NavierStokesSigmaStretchData K_max) :
    NavierStokesProjectedLpCoreData K_max where
  projData := ns.projData
  vorticityLp := ns.vorticityLp
  sigmaLp := fun k => MeasureTheory.MemLp.toLp (sigmaFromOpNorm ns.Sop k) (ns.sigma_mem k)
  stretchLp := ns.stretchLp
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  stretch_dom := ns.stretch_dom

#check @toProjectedLpCoreData

/-- Therefore the final PDE-facing sigma/stretch data already suffice to yield the
abstract `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_sigmaStretch
    {K_max : ℕ}
    (ns : NavierStokesSigmaStretchData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData (toLpCoreData (toProjectedLpCoreData ns))))
      (strainState (toLpCoreData (toProjectedLpCoreData ns))) := by
  exact
    NSNavierStokesProjectedCore.productionFromStrainSup_of_projected_core
      (toProjectedLpCoreData ns)

#check @productionFromStrainSup_of_sigmaStretch

end NSActualSigmaStretch
