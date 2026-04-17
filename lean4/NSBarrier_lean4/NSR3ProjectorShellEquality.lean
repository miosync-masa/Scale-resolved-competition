import NSBarrier.NSR3NavierStokesFields
import NSBarrier.NSR3ProjectorContraction
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3ProjectorShellEquality

open NSR3ShellActual

/-- Actual Euclidean PDE-facing data with the concrete shell projector family
baked in, together with an explicit shellwise projector identity. -/
structure R3ActualProjectedFieldData (K_max : ℕ) where
  vorticity : R3 → NSR3NavierStokesFields.Vec3
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3

  shellOmega : Fin K_max → R3 → NSR3NavierStokesFields.Vec3
  shellOmega_mem : ∀ k : Fin K_max, MemLp (shellOmega k) (2 : ℝ≥0∞) μR3

  sigma : Fin K_max → R3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MemLp (sigma k) ⊤ μR3
  sigmaOmegaLp : Fin K_max → NSR3NavierStokesFields.L2VecR3

  stretch : Fin K_max → R3 → NSR3NavierStokesFields.Vec3
  stretch_mem : ∀ k : Fin K_max, MemLp (stretch k) (2 : ℝ≥0∞) μR3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  sigma_bound :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (sigma k) (sigma_mem k)‖ ≤ strainSup

  stretch_dom :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (stretch k) (stretch_mem k)‖ ≤ ‖sigmaOmegaLp k‖

  shellOmega_eq_proj :
    ∀ k : Fin K_max,
      MemLp.toLp (shellOmega k) (shellOmega_mem k)
        =
      NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
        (MemLp.toLp vorticity vorticity_mem)

/-- Forget the explicit shell fields and feed the remaining data into the
existing Euclidean projected-field interface. -/
noncomputable def toR3NavierStokesProjectedFieldData
    {K_max : ℕ}
    (ns : R3ActualProjectedFieldData K_max) :
    NSR3NavierStokesFields.R3NavierStokesProjectedFieldData K_max where
  projData := NSR3LittlewoodPaleyActual.actualR3ShellProjectorData (K_max := K_max)
  vorticity := ns.vorticity
  vorticity_mem := ns.vorticity_mem
  sigma := ns.sigma
  sigma_mem := ns.sigma_mem
  sigmaOmegaLp := ns.sigmaOmegaLp
  stretch := ns.stretch
  stretch_mem := ns.stretch_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  stretch_dom := ns.stretch_dom

/-- The canonical `shellOmegaLp` attached to the actual Euclidean projector
family is literally the actual shell projector applied to the full vorticity. -/
theorem shellOmegaLp_eq_projector_of_R3_actual
    {K_max : ℕ}
    (ns : R3ActualProjectedFieldData K_max)
    (k : Fin K_max) :
    NSR3NavierStokesFields.shellOmegaLp (toR3NavierStokesProjectedFieldData ns) k =
      NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
        (MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  rfl

/-- The explicit shell field stored in the actual Euclidean data is identified
with the same projector image. -/
theorem shellOmega_toLp_eq_projector_of_R3_actual
    {K_max : ℕ}
    (ns : R3ActualProjectedFieldData K_max)
    (k : Fin K_max) :
    MemLp.toLp (ns.shellOmega k) (ns.shellOmega_mem k)
      =
    NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
      (MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  exact ns.shellOmega_eq_proj k

/-- The actual Euclidean projector package can be fed straight into the
existing `R³` field-interface wrapper theorem. -/
theorem R3_actual_field_interface_of_actual_projector
    {K_max : ℕ}
    (ns : R3ActualProjectedFieldData K_max) :
    ∃ vorticityLp : NSR3NavierStokesFields.L2VecR3,
      vorticityLp = MemLp.toLp ns.vorticity ns.vorticity_mem ∧
      (∀ k : Fin K_max,
        ‖MemLp.toLp (ns.stretch k) (ns.stretch_mem k)‖ ≤ ‖ns.sigmaOmegaLp k‖) := by
  simpa [toR3NavierStokesProjectedFieldData] using
    NSR3NavierStokesFields.R3_actual_field_interface
      (toR3NavierStokesProjectedFieldData ns)

end NSR3ProjectorShellEquality
