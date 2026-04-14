import NSBarrier.NSActualSigmaBoundProof
import NSBarrier.NSActualStretchDomProof
import NSBarrier.NSNavierStokesFields
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData T3)
open NSStrainOpVectorActual
open NSActualSigmaBound
open NSActualSigmaBoundProof
open NSActualStretchDomProof
open NSNavierStokesLpCore
open NSNavierStokesProjectedCore
open NSNavierStokesFields
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSActualTrueFields

-- ============================================================
-- SECTION 1: TRUE ACTUAL FIELD DATA
-- ============================================================

/-- True actual Navier–Stokes field data on `T³`, reduced to the final
PDE-facing obligations.

Here the scalar amplitude is no longer a free field:
it is canonically defined by `sigmaFromOpNorm Sop`.

The remaining nontrivial analytic inputs are:

- `sigma_mem` and `sigma_ae_bound` for `σ = ‖Sop‖op`;
- `sigmaOmega_mem` and `sigmaOmega_lp_eq` for the actual scalar-amplified
  shell field;
- `stretch_ae_dom`, i.e. a.e. pointwise domination of the actual stretching
  output by that scalar-amplified shell field.
-/
structure NavierStokesTrueFieldData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  /-- Full vorticity field. -/
  vorticity : T3 → Vec3
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  /-- Pointwise strain operator field. -/
  Sop : Fin K_max → T3 → Mat3

  /-- Actual stretching output field. -/
  stretch : Fin K_max → T3 → Vec3
  stretch_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (stretch k) (2 : ℝ≥0∞) μT3

  /-- Explicit scalar-amplified shell field. -/
  sigmaOmega : Fin K_max → T3 → Vec3
  sigmaOmega_mem :
    ∀ k : Fin K_max, MeasureTheory.MemLp (sigmaOmega k) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- `σ = ‖Sop‖op` belongs to `L∞(T³)`. -/
  sigma_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (sigmaFromOpNorm Sop k) ⊤ μT3

  /-- a.e. pointwise domination of the canonical sigma field by `strainSup`. -/
  sigma_ae_bound :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖sigmaFromOpNorm Sop k x‖ ≤ strainSup

  /-- The `Lp` class of `sigmaOmega k` is the scalar multiplication
      of the canonical sigma field with the actual shell-projected vorticity. -/
  sigmaOmega_lp_eq :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (sigmaOmega k) (sigmaOmega_mem k)
        =
      (MeasureTheory.MemLp.toLp (sigmaFromOpNorm Sop k) (sigma_mem k)) •
        (projData.Pk k (MeasureTheory.MemLp.toLp vorticity vorticity_mem))

  /-- a.e. pointwise domination of the actual stretching output
      by the scalar-amplified shell field. -/
  stretch_ae_dom :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖stretch k x‖ ≤ ‖sigmaOmega k x‖

#check @NavierStokesTrueFieldData

-- ============================================================
-- SECTION 2: BUILD THE TWO PROOF PACKAGES
-- ============================================================

/-- The actual sigma-bound proof package induced by the true field data. -/
noncomputable def toShellSigmaBoundProofData
    {K_max : ℕ}
    (ns : NavierStokesTrueFieldData K_max) :
    ShellSigmaBoundProofData K_max where
  Sop := ns.Sop
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_mem := ns.sigma_mem
  sigma_ae_bound := ns.sigma_ae_bound

#check @toShellSigmaBoundProofData

/-- The actual stretch-domination proof package induced by the true field data. -/
noncomputable def toShellStretchDomProofData
    {K_max : ℕ}
    (ns : NavierStokesTrueFieldData K_max) :
    ShellStretchDomProofData K_max where
  projData := ns.projData
  vorticity := ns.vorticity
  vorticity_mem := ns.vorticity_mem
  sigma := sigmaFromOpNorm ns.Sop
  sigma_mem := ns.sigma_mem
  stretch := ns.stretch
  stretch_mem := ns.stretch_mem
  sigmaOmega := ns.sigmaOmega
  sigmaOmega_mem := ns.sigmaOmega_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := by
    intro k
    rw [MeasureTheory.Lp.norm_toLp (f := sigmaFromOpNorm ns.Sop k) (hf := ns.sigma_mem k)]
    exact sigma_bound_of_ae_bound (toShellSigmaBoundProofData ns) k
  sigmaOmega_lp_eq := ns.sigmaOmega_lp_eq
  stretch_ae_dom := ns.stretch_ae_dom

#check @toShellStretchDomProofData

-- ============================================================
-- SECTION 3: FINAL BRIDGE TO THE BARRIER CHAIN
-- ============================================================

/-- The true actual field data already suffice to build the projected field data
used by the final barrier-facing bridge. -/
noncomputable def toNavierStokesProjectedFieldData
    {K_max : ℕ}
    (ns : NavierStokesTrueFieldData K_max) :
    NavierStokesProjectedFieldData K_max :=
  NSActualStretchDomProof.toNavierStokesProjectedFieldData
    (toShellStretchDomProofData ns)

#check @toNavierStokesProjectedFieldData

/-- Therefore the true actual field data already suffice to yield the abstract
`ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_true_fields
    {K_max : ℕ}
    (ns : NavierStokesTrueFieldData K_max) :
    let core := toLpCoreData (toProjectedLpCoreData
      (toNavierStokesProjectedFieldData ns))
    ProductionFromStrainSup
      (localizedProduction (localizedData core))
      (strainState core) := by
  exact
    productionFromStrainSup_of_field_data
      (toNavierStokesProjectedFieldData ns)

#check @productionFromStrainSup_of_true_fields

end NSActualTrueFields
