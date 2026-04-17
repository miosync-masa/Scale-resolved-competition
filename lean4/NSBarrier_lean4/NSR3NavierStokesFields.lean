import NSBarrier.NSR3LittlewoodPaley
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell

namespace NSR3NavierStokesFields

open NSR3ShellActual

noncomputable abbrev Vec3 := EuclideanSpace ℂ (Fin 3)
noncomputable abbrev Mat3 := Vec3 →L[ℂ] Vec3
noncomputable abbrev L2VecR3 :=
  MeasureTheory.Lp Vec3 (2 : ℝ≥0∞) μR3
noncomputable abbrev LInfScalarR3 :=
  MeasureTheory.Lp ℂ ⊤ μR3

noncomputable instance : InnerProductSpace ℝ L2VecR3 :=
  InnerProductSpace.rclikeToReal ℂ L2VecR3

/-- Function-level PDE-facing data on `R^3`, mirroring the torus-side projected
field interface but using the Euclidean `L²(R^3)` backend. -/
structure R3NavierStokesProjectedFieldData (K_max : ℕ) where
  projData : ShellProjectorData L2VecR3 K_max

  vorticity : R3 → Vec3
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3

  sigma : Fin K_max → R3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MemLp (sigma k) ⊤ μR3
  sigmaOmegaLp : Fin K_max → L2VecR3

  stretch : Fin K_max → R3 → Vec3
  stretch_mem : ∀ k : Fin K_max, MemLp (stretch k) (2 : ℝ≥0∞) μR3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup

  sigma_bound :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (sigma k) (sigma_mem k)‖ ≤ strainSup

  stretch_dom :
    ∀ k : Fin K_max,
      ‖MemLp.toLp (stretch k) (stretch_mem k)‖ ≤ ‖sigmaOmegaLp k‖

/-- The canonical shell-projected vorticity in the Euclidean branch. -/
noncomputable def shellOmegaLp
    {K_max : ℕ}
    (ns : R3NavierStokesProjectedFieldData K_max) :
    Fin K_max → L2VecR3 :=
  fun k => ns.projData.Pk k (MemLp.toLp ns.vorticity ns.vorticity_mem)

/-- The projected shell field is, by definition, the output of the Euclidean
projector family on the full vorticity field. -/
theorem shellOmegaLp_eq_projector_of_R3_field_data
    {K_max : ℕ}
    (ns : R3NavierStokesProjectedFieldData K_max)
    (k : Fin K_max) :
    shellOmegaLp ns k =
      ns.projData.Pk k (MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  rfl

/-- C4 field-interface theorem: Euclidean PDE-facing data provide a full
`L²(R^3)` vorticity state and shellwise `L²` domination of stretching by the
scalar-amplified projected shell field. -/
theorem R3_actual_field_interface
    {K_max : ℕ}
    (ns : R3NavierStokesProjectedFieldData K_max) :
    ∃ vorticityLp : L2VecR3,
      vorticityLp = MemLp.toLp ns.vorticity ns.vorticity_mem ∧
      (∀ k : Fin K_max,
        ‖MemLp.toLp (ns.stretch k) (ns.stretch_mem k)‖ ≤ ‖ns.sigmaOmegaLp k‖) := by
  refine ⟨MemLp.toLp ns.vorticity ns.vorticity_mem, rfl, ?_⟩
  intro k
  simpa using ns.stretch_dom k

end NSR3NavierStokesFields
