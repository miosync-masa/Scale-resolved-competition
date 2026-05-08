import NSBarrier.NSNavierStokesFields
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData T3)
open NSStrainOpVectorActual
open NSNavierStokesLpCore
open NSNavierStokesProjectedCore
open NSNavierStokesFields
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSActualStretchDomProof

-- ============================================================
-- SECTION 1: POINTWISE-TO-L² STRETCH DOMINATION DATA
-- ============================================================

/-- Data for proving `stretch_dom` from a.e. pointwise domination.

We keep an explicit function-level `sigmaOmega` representative so that
the `L²` domination theorem can be proved purely by `eLpNorm_mono_ae`,
and only afterwards identify its `Lp` class with
  `(toLp sigma) • (Pk (toLp vorticity))`.
-/
structure ShellStretchDomProofData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticity : T3 → Vec3
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  sigma : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3

  stretch : Fin K_max → T3 → Vec3
  stretch_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (stretch k) (2 : ℝ≥0∞) μT3

  /-- Explicit representative of the scalar-amplified shell field. -/
  sigmaOmega : Fin K_max → T3 → Vec3
  sigmaOmega_mem :
    ∀ k : Fin K_max, MeasureTheory.MemLp (sigmaOmega k) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- The scalar amplitude proxy is bounded by `strainSup` in `L∞`. -/
  sigma_bound :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (sigma k) (sigma_mem k)‖ ≤ strainSup

  /-- The `Lp` class of `sigmaOmega k` is exactly
      `(toLp sigma k) • (Pk (toLp vorticity))`. -/
  sigmaOmega_lp_eq :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (sigmaOmega k) (sigmaOmega_mem k)
        =
      (MeasureTheory.MemLp.toLp (sigma k) (sigma_mem k)) •
        (projData.Pk k (MeasureTheory.MemLp.toLp vorticity vorticity_mem))

  /-- a.e. pointwise domination of the actual stretching output
      by the scalar-amplified shell field. -/
  stretch_ae_dom :
    ∀ k : Fin K_max, ∀ᵐ x ∂ μT3,
      ‖stretch k x‖ ≤ ‖sigmaOmega k x‖

#check @ShellStretchDomProofData

-- ============================================================
-- SECTION 2: a.e. DOMINATION -> L² DOMINATION
-- ============================================================

/-- Actual `L²` domination of the stretching output by the scalar-amplified shell field. -/
theorem stretch_dom_of_ae_bound
    {K_max : ℕ}
    (sad : ShellStretchDomProofData K_max) :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp (sad.stretch k) (sad.stretch_mem k)‖ ≤
        ‖MeasureTheory.MemLp.toLp (sad.sigmaOmega k) (sad.sigmaOmega_mem k)‖ := by
  intro k
  rw [MeasureTheory.Lp.norm_toLp (f := sad.stretch k) (hf := sad.stretch_mem k),
      MeasureTheory.Lp.norm_toLp (f := sad.sigmaOmega k) (hf := sad.sigmaOmega_mem k)]
  exact ENNReal.toReal_mono
    (ne_of_lt (sad.sigmaOmega_mem k).eLpNorm_lt_top)
    (MeasureTheory.eLpNorm_mono_ae (sad.stretch_ae_dom k))

#check @stretch_dom_of_ae_bound

-- ============================================================
-- SECTION 3: BUILD THE PROJECTED FIELD DATA
-- ============================================================

/-- Build the projected-field data needed by the downstream actual barrier chain. -/
noncomputable def toNavierStokesProjectedFieldData
    {K_max : ℕ}
    (sad : ShellStretchDomProofData K_max) :
    NavierStokesProjectedFieldData K_max where
  projData := sad.projData
  vorticity := sad.vorticity
  vorticity_mem := sad.vorticity_mem
  sigma := sad.sigma
  sigma_mem := sad.sigma_mem
  stretch := sad.stretch
  stretch_mem := sad.stretch_mem
  strainSup := sad.strainSup
  strainSup_nonneg := sad.strainSup_nonneg
  sigma_bound := sad.sigma_bound
  stretch_dom := by
    intro k
    have hdom :
        ‖MeasureTheory.MemLp.toLp (sad.stretch k) (sad.stretch_mem k)‖ ≤
          ‖MeasureTheory.MemLp.toLp (sad.sigmaOmega k) (sad.sigmaOmega_mem k)‖ :=
      stretch_dom_of_ae_bound sad k
    rw [sad.sigmaOmega_lp_eq k] at hdom
    exact hdom

#check @toNavierStokesProjectedFieldData

-- ============================================================
-- SECTION 4: FINAL BRIDGE
-- ============================================================

/-- Therefore the pointwise stretch domination data already yield the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_stretchDom
    {K_max : ℕ}
    (sad : ShellStretchDomProofData K_max) :
    let core := toLpCoreData (toProjectedLpCoreData
      (toNavierStokesProjectedFieldData sad))
    ProductionFromStrainSup
      (localizedProduction (localizedData core))
      (strainState core) := by
  exact
    productionFromStrainSup_of_field_data
      (toNavierStokesProjectedFieldData sad)

#check @productionFromStrainSup_of_stretchDom

end NSActualStretchDomProof
