import NSBarrier.NSTorusShell
import NSBarrier.NSStrainAction
import NSBarrier.NSStrainOpVectorActual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell
open NSStrainAction
open NSStrainOpVectorActual
open NSFourier
open NSAnalyticA
open NSAnalyticA1Locality

namespace NSVorticityTransportActualVec

-- `InnerProductSpace ℝ L2VecT3` is not an instance in Mathlib (rclikeToReal is a
-- reducible non-instance to avoid diamonds). We provide it here.
noncomputable instance : InnerProductSpace ℝ L2VecT3 :=
  InnerProductSpace.rclikeToReal ℂ L2VecT3

-- ℂ-linear maps on L2VecT3 can be restricted to ℝ-linear maps.
instance : LinearMap.CompatibleSMul L2VecT3 L2VecT3 ℝ ℂ where
  map_smul fₗ r x := fₗ.map_smul (r : ℂ) x

-- ============================================================
-- SECTION 1: TRUE NAVIER–STOKES SHELL TRANSPORT DATA
-- ============================================================

/-- Actual shellwise Navier–Stokes transport data on `T³`, in vector form.

This is the final PDE-facing package:
- `vorticity` is the full vorticity field ω
- `shellOmega k` is the shell-projected vorticity ω_k
- `Sop k x` is the actual pointwise strain operator acting on ω_k(x)
- the shellwise stretching output is `x ↦ Sop k x (shellOmega k x)`
- `action_le` is the actual `L²` control
  ‖Z_k‖_{L²} ≤ strainSup · ‖ω_k‖_{L²}
- `shellOmega_eq_proj` identifies ω_k with the actual shell projector applied
  to the full vorticity in the chosen Hilbert-space shell decomposition.
-/
structure NavierStokesShellTransportVecData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticity : T3 → Vec3
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  shellOmega : Fin K_max → T3 → Vec3
  shellOmega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (shellOmega k) (2 : ℝ≥0∞) μT3

  sigma : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3

  Sop : Fin K_max → T3 → Mat3
  stretch_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => (Sop k x) (shellOmega k x)) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

  op_bound :
    ∀ k : Fin K_max, ∀ x : T3, ‖Sop k x‖ ≤ ‖sigma k x‖

  /-- Actual `L²` shellwise strain-action estimate. -/
  action_le :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp
          (fun x => (Sop k x) (shellOmega k x))
          (stretch_mem k)‖
        ≤
      strainSup * ‖MeasureTheory.MemLp.toLp (shellOmega k) (shellOmega_mem k)‖

  /-- Actual shell-projected vorticity identity. -/
  shellOmega_eq_proj :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (shellOmega k) (shellOmega_mem k)
        =
      projData.Pk k (MeasureTheory.MemLp.toLp vorticity vorticity_mem)

#check @NavierStokesShellTransportVecData

-- ============================================================
-- SECTION 2: BRIDGE TO THE VECTOR A1 CHAIN
-- ============================================================

/-- Convert PDE-facing transport data into the generic shell strain-action data
    used by the already-proved vector A1 chain. -/
noncomputable def toShellStrainActionData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    ShellStrainActionData L2VecT3 K_max where
  projData := ns.projData
  omega := fun k => MeasureTheory.MemLp.toLp (ns.shellOmega k) (ns.shellOmega_mem k)
  Z := fun k =>
    MeasureTheory.MemLp.toLp
      (fun x => (ns.Sop k x) (ns.shellOmega k x))
      (ns.stretch_mem k)
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  action_le := ns.action_le

#check @toShellStrainActionData

/-- The corresponding localized shell data. -/
noncomputable def localizedData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    ShellLocalizedData L2VecT3 K_max :=
  NSStrainAction.localizedData (toShellStrainActionData ns)

/-- The corresponding Fourier state. -/
noncomputable def strainState
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    FourierState K_max :=
  NSStrainAction.strainState (toShellStrainActionData ns)

#check @localizedData
#check @strainState

/-- Therefore the actual shellwise Navier–Stokes transport data yield
    `LocalizedProjectedStretching`. -/
theorem localizedProjectedStretching_of_navierStokes_transport
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    LocalizedProjectedStretching
      (localizedProduction (localizedData ns))
      (strainState ns)
      (toGradientAmplitude (localizedData ns)) := by
  simpa [localizedData, strainState] using
    (NSStrainAction.localizedProjectedStretching_of_strain_action
      (toShellStrainActionData ns))

/-- Since `gradAmp = strainSup`, gradient control by strain holds with constant `1`. -/
theorem gradientControlledByStrain_of_navierStokes_transport
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    GradientControlledByStrain
      (strainState ns)
      (toGradientAmplitude (localizedData ns))
      1 := by
  simpa [localizedData, strainState] using
    (NSStrainAction.gradientControlledByStrain_of_strain_action
      (toShellStrainActionData ns))

/-- The actual shellwise Navier–Stokes transport data yield the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_navierStokes_transport
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData ns))
      (strainState ns) := by
  simpa [localizedData, strainState] using
    (NSStrainAction.productionFromStrainSup_of_strain_action
      (toShellStrainActionData ns))

#check @localizedProjectedStretching_of_navierStokes_transport
#check @gradientControlledByStrain_of_navierStokes_transport
#check @productionFromStrainSup_of_navierStokes_transport

-- ============================================================
-- SECTION 3: EXPOSE THE ACTUAL SHELL-VORTICITY IDENTITY
-- ============================================================

/-- The packaged shell field is indeed the shell projection of the full vorticity. -/
theorem shellOmega_toLp_eq_projector
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecData K_max)
    (k : Fin K_max) :
    MeasureTheory.MemLp.toLp (ns.shellOmega k) (ns.shellOmega_mem k)
      =
    ns.projData.Pk k
      (MeasureTheory.MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  exact ns.shellOmega_eq_proj k

#check @shellOmega_toLp_eq_projector

end NSVorticityTransportActualVec
