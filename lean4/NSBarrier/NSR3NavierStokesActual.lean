import NSBarrier.NSR3ActualTrueFields
import NSBarrier.NSStrainAction
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3NavierStokesActual

open NSAnalyticA
open NSAnalyticA1Locality
open NSFourier
open NSR3ActualTrueFields
open NSR3MinimalPDEFrontier
open NSR3ShellActual
open NSStrainAction

/-- Convert actual Euclidean true fields into the shellwise strain-action data
used by the abstract barrier chain. -/
noncomputable def toR3ShellStrainActionData
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    ShellStrainActionData NSR3NavierStokesFields.L2VecR3 K_max where
  projData := NSR3LittlewoodPaleyActual.actualR3ShellProjectorData (K_max := K_max)
  omega := fun k =>
    NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
      (MemLp.toLp ns.vorticity ns.vorticity_mem)
  Z := fun k => MemLp.toLp (ns.stretch k) (ns.stretch_mem k)
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  action_le := by
    intro k
    have hdom :
        ‖MemLp.toLp (ns.stretch k) (ns.stretch_mem k)‖ ≤ ‖ns.sigmaOmegaLp k‖ :=
      ns.stretch_dom k
    have hsmul :
        ‖ns.sigmaOmegaLp k‖
          ≤
        ‖MemLp.toLp (sigmaFromOpNormR3 ns.Sop k) (ns.sigma_mem k)‖
          * ‖NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
              (MemLp.toLp ns.vorticity ns.vorticity_mem)‖ := by
      rw [ns.sigmaOmegaLp_eq k]
      simpa using
        (MeasureTheory.Lp.norm_smul_le
          (MemLp.toLp (sigmaFromOpNormR3 ns.Sop k) (ns.sigma_mem k))
          (NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
            (MemLp.toLp ns.vorticity ns.vorticity_mem)))
    have hsigma :
        ‖MemLp.toLp (sigmaFromOpNormR3 ns.Sop k) (ns.sigma_mem k)‖ ≤ ns.strainSup :=
      sigma_Linfty_bound_of_true_fields_R3 ns k
    exact
      le_trans hdom <|
        le_trans hsmul <|
          mul_le_mul_of_nonneg_right hsigma
            (norm_nonneg
              (NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
                (MemLp.toLp ns.vorticity ns.vorticity_mem)))

/-- Therefore actual Euclidean true fields yield the abstract
`ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_R3_true_fields
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max) :
    ProductionFromStrainSup
      (localizedProduction (localizedData (toR3ShellStrainActionData ns)))
      (strainState (toR3ShellStrainActionData ns)) := by
  simpa using
    NSStrainAction.productionFromStrainSup_of_strain_action
      (toR3ShellStrainActionData ns)

/-- The packaged Euclidean shell field is indeed the actual shell projection
of the full vorticity field. -/
theorem shellOmega_toLp_eq_actual_projector_of_R3_true_fields
    {K_max : ℕ}
    (ns : R3NavierStokesTrueFieldData K_max)
    (k : Fin K_max) :
    MemLp.toLp (ns.shellOmega k) (ns.shellOmega_mem k)
      =
    NSR3LittlewoodPaleyActual.actualR3ShellProjFamily (K_max := K_max) k
      (MemLp.toLp ns.vorticity ns.vorticity_mem) := by
  exact ns.shellOmega_eq_proj k

end NSR3NavierStokesActual
