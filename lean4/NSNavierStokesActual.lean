import NSBarrier.NSTorusShellModes
import NSBarrier.NSStrainOpActual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSTorusShellModes
open NSL2MultiplierTorus
open NSStrainOpActual
open NSVorticityTransportActual
open NSStrainTensorActual
open NSL2MultiplierActual
open NSFourier
open NSAnalyticA1Locality

namespace NSNavierStokesActual

-- ============================================================
-- SECTION 1: ACTUAL NAVIER–STOKES SHELL DATA ON T³
-- ============================================================

/-- Actual Navier–Stokes shell data on `T³`, packaged so that it can be fed into
the already-established actual strain-operator chain.

At this stage, we do **not** formalize the full PDE.  Instead, we isolate exactly
the actual data needed to instantiate `ShellStrainOperatorData`:

- `vorticity` is the full vorticity field on `T³`
- `shellOmega k` is the shell-projected vorticity component
- `sigma k` is the scalar amplitude proxy, intended to be `‖S(·)‖op`
- `Sop k x` is the pointwise strain operator acting on the shell field
- `stretch_mem` states that `x ↦ Sop k x (shellOmega k x)` is an `L²` field
- `shellOmega_eq_proj` identifies `shellOmega k` with the actual shell projector
  applied to the full vorticity field in `L²`.
-/
structure NavierStokesShellData (K_max : ℕ) where
  vorticity : T3 → ℂ
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  shellOmega : Fin K_max → T3 → ℂ
  shellOmega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (shellOmega k) (2 : ℝ≥0∞) μT3

  sigma : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3

  Sop : Fin K_max → T3 → (ℂ →L[ℂ] ℂ)

  /-- The shellwise stretching output is `x ↦ Sop_k(x)(ω_k(x))`. -/
  stretch_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => (Sop k x) (shellOmega k x)) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

  /-- Pointwise operator-amplitude control. -/
  op_bound :
    ∀ k : Fin K_max, ∀ x : T3, ‖Sop k x‖ ≤ ‖sigma k x‖

  /-- The shell field is the actual shell projector applied to the full vorticity. -/
  shellOmega_eq_proj :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (shellOmega k) (shellOmega_mem k)
        =
      actualShellProjFamily (K_max := K_max) k
        (MeasureTheory.MemLp.toLp vorticity vorticity_mem)

#check @NavierStokesShellData

-- ============================================================
-- SECTION 2: BRIDGE TO ACTUAL STRAIN-OPERATOR DATA
-- ============================================================

/-- Convert actual Navier–Stokes shell data into the actual operator-valued
strain data used by `NSStrainOpActual`. -/
noncomputable def toShellStrainOperatorData
    {K_max : ℕ}
    (ns : NavierStokesShellData K_max) :
    ShellStrainOperatorData K_max where
  sigma := ns.sigma
  omega := ns.shellOmega
  Sop := ns.Sop
  sigma_mem := ns.sigma_mem
  omega_mem := ns.shellOmega_mem
  Z_mem := ns.stretch_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  op_bound := ns.op_bound

#check @toShellStrainOperatorData

/-- Therefore actual Navier–Stokes shell data yield the abstract
`ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_navierStokes_shell
    {K_max : ℕ}
    (ns : NavierStokesShellData K_max) :
    ProductionFromStrainSup
      (localizedProduction
        (actualLocalizedData
          (toActualShellStrainActionData
            (toScalarReductionData
              (toShellPointwiseStrainActionData
                (toShellStrainOperatorData ns))))))
      (actualStrainState
        (toActualShellStrainActionData
          (toScalarReductionData
            (toShellPointwiseStrainActionData
              (toShellStrainOperatorData ns))))) := by
  exact
    productionFromStrainSup_of_strain_operator
      (toShellStrainOperatorData ns)

#check @productionFromStrainSup_of_navierStokes_shell

-- ============================================================
-- SECTION 3: EXPOSE THE ACTUAL SHELL-PROJECTED VORTICITY FACT
-- ============================================================

/-- The packaged shell field is indeed the actual shell projection
of the full vorticity field. -/
theorem shellOmega_toLp_eq_actual_projector
    {K_max : ℕ}
    (ns : NavierStokesShellData K_max)
    (k : Fin K_max) :
    MeasureTheory.MemLp.toLp (ns.shellOmega k) (ns.shellOmega_mem k)
      =
    actualShellProjFamily (K_max := K_max) k
      (MeasureTheory.MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  exact ns.shellOmega_eq_proj k

#check @shellOmega_toLp_eq_actual_projector

end NSNavierStokesActual
