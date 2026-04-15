import NSBarrier.NSVorticityTransportActualVec
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData)
open NSStrainAction
open NSStrainOpVectorActual
open NSVorticityTransportActualVec
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSNavierStokesLpCore

/-- Scalar `L∞(T³)` amplitudes. -/
noncomputable abbrev LInfScalarT3 :=
  MeasureTheory.Lp ℂ ⊤ μT3

-- ============================================================
-- SECTION 1: Lp-LEVEL CORE PDE DATA
-- ============================================================

/-- `Lp`-level actual Navier–Stokes shell transport core data.

This is the bookkeeping-light version of the PDE-facing package:
- `vorticityLp` is the full vorticity field in `L²(T³; ℂ³)`
- `shellOmegaLp k` is the shell-projected vorticity
- `sigmaLp k` is the scalar amplitude proxy in `L∞(T³)`
- `sigmaOmegaLp k` is the actual scalar-multiplied shell field
- `stretchLp k` is the actual shellwise stretching output in `L²`

The key point is that several former function-level fields disappear:
- `shellOmega_eq_proj` becomes an `Lp` equality field
- `sigmaOmega_mem` disappears because `sigmaOmegaLp` is already an `Lp` element
- `stretch_mem` disappears because `stretchLp` is already an `Lp` element
- `action_le` will be derived from `stretch_dom` + `norm_smul_le`.
-/
structure NavierStokesShellTransportVecLpCoreData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticityLp : L2VecT3
  sigmaLp : Fin K_max → LInfScalarT3
  shellOmegaLp : Fin K_max → L2VecT3
  sigmaOmegaLp : Fin K_max → L2VecT3
  stretchLp : Fin K_max → L2VecT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- `sigmaLp` is bounded by `strainSup` in `L∞`. -/
  sigma_bound :
    ∀ k : Fin K_max, ‖sigmaLp k‖ ≤ strainSup

  /-- `shellOmegaLp` is the actual shell projection of the full vorticity. -/
  shellOmega_def :
    ∀ k : Fin K_max,
      shellOmegaLp k = projData.Pk k vorticityLp

  /-- `sigmaOmegaLp` is the actual scalar multiplication of `shellOmegaLp`. -/
  sigmaOmega_def :
    ∀ k : Fin K_max,
      sigmaOmegaLp k = sigmaLp k • shellOmegaLp k

  /-- `stretchLp` is dominated by the scalar-multiplied shell field. -/
  stretch_dom :
    ∀ k : Fin K_max,
      ‖stretchLp k‖ ≤ ‖sigmaOmegaLp k‖

#check @NavierStokesShellTransportVecLpCoreData

-- ============================================================
-- SECTION 2: DERIVE action_le AT THE Lp LEVEL
-- ============================================================

/-- The actual `L²` shellwise strain-action estimate derived from
the `Lp`-level scalar multiplier control. -/
theorem action_le_of_LpCore
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    ∀ k : Fin K_max,
      ‖ns.stretchLp k‖ ≤ ns.strainSup * ‖ns.shellOmegaLp k‖ := by
  intro k
  have hdom : ‖ns.stretchLp k‖ ≤ ‖ns.sigmaOmegaLp k‖ :=
    ns.stretch_dom k
  have hsmul :
      ‖ns.sigmaOmegaLp k‖ ≤ ‖ns.sigmaLp k‖ * ‖ns.shellOmegaLp k‖ := by
    rw [ns.sigmaOmega_def k]
    simpa using (MeasureTheory.Lp.norm_smul_le (ns.sigmaLp k) (ns.shellOmegaLp k))
  exact le_trans hdom <|
    le_trans hsmul <|
      mul_le_mul_of_nonneg_right
        (ns.sigma_bound k)
        (norm_nonneg (ns.shellOmegaLp k))

#check @action_le_of_LpCore

-- ============================================================
-- SECTION 3: BRIDGE TO THE EXISTING A1 CHAIN
-- ============================================================

/-- Convert the `Lp`-level core data into `ShellStrainActionData`. -/
noncomputable def toShellStrainActionData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    ShellStrainActionData L2VecT3 K_max where
  projData := ns.projData
  omega := ns.shellOmegaLp
  Z := ns.stretchLp
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  action_le := action_le_of_LpCore ns

#check @toShellStrainActionData

/-- The corresponding localized shell data. -/
noncomputable def localizedData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    ShellLocalizedData L2VecT3 K_max :=
  NSStrainAction.localizedData (toShellStrainActionData ns)

/-- The corresponding Fourier state. -/
noncomputable def strainState
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    FourierState K_max :=
  NSStrainAction.strainState (toShellStrainActionData ns)

#check @localizedData
#check @strainState

/-- Therefore the `Lp`-level core PDE data already yield
`LocalizedProjectedStretching`. -/
theorem localizedProjectedStretching_of_LpCore
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData ns))
      (strainState ns)
      (toGradientAmplitude (localizedData ns)) := by
  simpa [localizedData, strainState] using
    (NSStrainAction.localizedProjectedStretching_of_strain_action
      (toShellStrainActionData ns))

/-- Since `gradAmp = strainSup`, gradient control by strain holds with constant `1`. -/
theorem gradientControlledByStrain_of_LpCore
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    GradientControlledByStrain
      (strainState ns)
      (toGradientAmplitude (localizedData ns))
      1 := by
  simpa [localizedData, strainState] using
    (NSStrainAction.gradientControlledByStrain_of_strain_action
      (toShellStrainActionData ns))

/-- The `Lp`-level core PDE data already suffice to yield the abstract
`ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_LpCore
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData ns))
      (strainState ns) := by
  simpa [localizedData, strainState] using
    (NSStrainAction.productionFromStrainSup_of_strain_action
      (toShellStrainActionData ns))

#check @localizedProjectedStretching_of_LpCore
#check @gradientControlledByStrain_of_LpCore
#check @productionFromStrainSup_of_LpCore

-- ============================================================
-- SECTION 4: EXPOSE THE ACTUAL SHELL-PROJECTION IDENTITY
-- ============================================================

/-- The packaged shell field is indeed the shell projection of the full vorticity. -/
theorem shellOmegaLp_eq_projector
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max)
    (k : Fin K_max) :
    ns.shellOmegaLp k = ns.projData.Pk k ns.vorticityLp := by
  exact ns.shellOmega_def k

#check @shellOmegaLp_eq_projector

end NSNavierStokesLpCore
