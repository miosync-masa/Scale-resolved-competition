import NSBarrier.NSNavierStokesProjectedCore
import NSBarrier.NSNavierStokesLpCore
import Mathlib.Tactic

open NSTorusShell (ShellProjectorData)
open NSStrainOpVectorActual

namespace NSVorticityMembershipTheorems

open NSNavierStokesProjectedCore
open NSNavierStokesLpCore

-- ============================================================
-- [Alg] Vorticity membership and shell-omega membership theorems
--
-- These make explicit that vorticity_mem and shellOmega_mem
-- are NOT external PDE assumptions when working at the Lp level:
-- they are consequences of the type system (Lp elements) and
-- projector contraction.
-- ============================================================

/-- [Alg] At the Lp level, vorticityLp is already an L2 element
by typing — no `vorticity_mem` assumption needed.

This theorem expresses that the vorticity norm is a real number
(finite by the Lp typing). -/
theorem vorticityLp_norm_nonneg
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    0 ≤ ‖ns.vorticityLp‖ :=
  norm_nonneg _

/-- [Alg] The shell-projected vorticity has norm bounded by
the full vorticity norm, by projector contraction.

This shows that `shellOmega_mem` is a consequence of
`vorticityLp ∈ L²` (which is by typing) plus projector
contraction — not an independent assumption. -/
theorem shellOmegaLp_norm_le_of_projector_contraction
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      ‖shellOmegaLp ns k‖ ≤ ‖ns.vorticityLp‖ := by
  intro k
  rw [shellOmegaLp_eq_projector ns k]
  exact (ns.projData.proj_contraction k) ns.vorticityLp

/-- [Alg] Sigma-omega Lp norm is bounded by sigma norm times
shell-projected vorticity norm. -/
theorem sigmaOmegaLp_norm_le_of_projector_contraction
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      ‖sigmaOmegaLp ns k‖
        ≤ ‖ns.sigmaLp k‖ * ‖shellOmegaLp ns k‖ := by
  intro k
  rw [sigmaOmegaLp_eq_smul ns k]
  simpa using MeasureTheory.Lp.norm_smul_le
    (ns.sigmaLp k) (shellOmegaLp ns k)

/-- [Alg] The Lp-level action_le follows from stretch_dom +
sigma_bound + projector contraction. This theorem makes
explicit that `action_le` is a derived theorem, not an
external assumption. -/
theorem action_le_of_lp_projector_contraction
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      ‖ns.stretchLp k‖
        ≤ ns.strainSup * ‖shellOmegaLp ns k‖ :=
  action_le_of_projected_core ns

/-- [Alg] At the Lp level, the shell-projection identity is
definitional — shellOmegaLp is *defined* as Pk(vorticityLp). -/
theorem shellOmega_is_projection_of_definition
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      shellOmegaLp ns k = ns.projData.Pk k ns.vorticityLp :=
  shellOmegaLp_eq_projector ns

#check @vorticityLp_norm_nonneg
#check @shellOmegaLp_norm_le_of_projector_contraction
#check @sigmaOmegaLp_norm_le_of_projector_contraction
#check @action_le_of_lp_projector_contraction
#check @shellOmega_is_projection_of_definition

end NSVorticityMembershipTheorems
