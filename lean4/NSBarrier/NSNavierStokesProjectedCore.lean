import NSBarrier.NSNavierStokesLpCore
import Mathlib.Tactic

open NSTorusShell (ShellProjectorData)
open NSStrainOpVectorActual
open NSNavierStokesLpCore
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSNavierStokesProjectedCore

/-- A thinner PDE-facing `Lp` core package:
    shell-projected vorticity and scalar-multiplied shell fields are not fields anymore;
    they are defined canonically from the projector family, the full vorticity,
    and the scalar amplitude. -/
structure NavierStokesProjectedLpCoreData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max
  vorticityLp : L2VecT3
  sigmaLp : Fin K_max → LInfScalarT3
  stretchLp : Fin K_max → L2VecT3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  /-- `sigmaLp` is bounded by `strainSup` in `L∞`. -/
  sigma_bound :
    ∀ k : Fin K_max, ‖sigmaLp k‖ ≤ strainSup

  /-- The actual stretching output is dominated by the scalar-multiplied shell field. -/
  stretch_dom :
    ∀ k : Fin K_max,
      ‖stretchLp k‖ ≤ ‖sigmaLp k • (projData.Pk k vorticityLp)‖

#check @NavierStokesProjectedLpCoreData

-- ============================================================
-- SECTION 1: CANONICAL PROJECTED FIELDS
-- ============================================================

/-- The canonical shell-projected vorticity field. -/
noncomputable def shellOmegaLp
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    Fin K_max → L2VecT3 :=
  fun k => ns.projData.Pk k ns.vorticityLp

/-- The canonical scalar-multiplied shell field. -/
noncomputable def sigmaOmegaLp
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    Fin K_max → L2VecT3 :=
  fun k => ns.sigmaLp k • shellOmegaLp ns k

@[simp] theorem shellOmegaLp_eq_projector
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max)
    (k : Fin K_max) :
    shellOmegaLp ns k = ns.projData.Pk k ns.vorticityLp := rfl

@[simp] theorem sigmaOmegaLp_eq_smul
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max)
    (k : Fin K_max) :
    sigmaOmegaLp ns k = ns.sigmaLp k • shellOmegaLp ns k := rfl

#check @shellOmegaLp
#check @sigmaOmegaLp
#check @shellOmegaLp_eq_projector
#check @sigmaOmegaLp_eq_smul

-- ============================================================
-- SECTION 2: DERIVE action_le
-- ============================================================

/-- The shellwise `L²` strain-action estimate is now a theorem,
    not a field, obtained from the scalar `Lp` multiplier control. -/
theorem action_le_of_projected_core
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      ‖ns.stretchLp k‖ ≤ ns.strainSup * ‖shellOmegaLp ns k‖ := by
  intro k
  have hdom : ‖ns.stretchLp k‖ ≤ ‖sigmaOmegaLp ns k‖ := by
    simpa [sigmaOmegaLp, shellOmegaLp] using ns.stretch_dom k
  have hsmul :
      ‖sigmaOmegaLp ns k‖ ≤ ‖ns.sigmaLp k‖ * ‖shellOmegaLp ns k‖ := by
    rw [sigmaOmegaLp_eq_smul]
    simpa using (MeasureTheory.Lp.norm_smul_le (ns.sigmaLp k) (shellOmegaLp ns k))
  exact le_trans hdom <|
    le_trans hsmul <|
      mul_le_mul_of_nonneg_right
        (ns.sigma_bound k)
        (norm_nonneg (shellOmegaLp ns k))

#check @action_le_of_projected_core

-- ============================================================
-- SECTION 3: BRIDGE TO NSNavierStokesLpCore
-- ============================================================

/-- The thinner projected core package induces the previous `Lp` core package. -/
noncomputable def toLpCoreData
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    NavierStokesShellTransportVecLpCoreData K_max where
  projData := ns.projData
  vorticityLp := ns.vorticityLp
  sigmaLp := ns.sigmaLp
  shellOmegaLp := shellOmegaLp ns
  sigmaOmegaLp := sigmaOmegaLp ns
  stretchLp := ns.stretchLp
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  shellOmega_def := by
    intro k
    exact shellOmegaLp_eq_projector ns k
  sigmaOmega_def := by
    intro k
    exact sigmaOmegaLp_eq_smul ns k
  stretch_dom := by
    intro k
    simpa [sigmaOmegaLp, shellOmegaLp] using ns.stretch_dom k

#check @toLpCoreData

/-- Therefore the projected `Lp` core already yields the abstract
    `LocalizedProjectedStretching` needed by the barrier chain. -/
theorem localizedProjectedStretching_of_projected_core
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData (toLpCoreData ns)))
      (strainState (toLpCoreData ns))
      (toGradientAmplitude (localizedData (toLpCoreData ns))) := by
  exact NSNavierStokesLpCore.localizedProjectedStretching_of_LpCore (toLpCoreData ns)

/-- Gradient control by strain holds with constant `1` for the projected `Lp` core. -/
theorem gradientControlledByStrain_of_projected_core
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    GradientControlledByStrain
      (strainState (toLpCoreData ns))
      (toGradientAmplitude (localizedData (toLpCoreData ns)))
      1 := by
  exact NSNavierStokesLpCore.gradientControlledByStrain_of_LpCore (toLpCoreData ns)

/-- The projected `Lp` core already suffices to produce
    the abstract `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_projected_core
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData (toLpCoreData ns)))
      (strainState (toLpCoreData ns)) := by
  exact NSNavierStokesLpCore.productionFromStrainSup_of_LpCore (toLpCoreData ns)

#check @localizedProjectedStretching_of_projected_core
#check @gradientControlledByStrain_of_projected_core
#check @productionFromStrainSup_of_projected_core

end NSNavierStokesProjectedCore
