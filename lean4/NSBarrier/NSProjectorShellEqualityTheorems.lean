import NSBarrier.NSAveragedBudgetRelationTheorems
import NSBarrier.NSNavierStokesProjectedCore
import NSBarrier.NSNavierStokesLpCore
import NSBarrier.NSTorusShellActual
import NSBarrier.NSTorusShellFinite
import Mathlib.Tactic

open NSTorusShell (ShellProjectorData)
open NSStrainOpVectorActual

namespace NSProjectorShellEqualityTheorems

open NSNavierStokesProjectedCore
open NSNavierStokesLpCore
open NSTorusShellActual
open NSTorusShellFinite

-- ============================================================
-- Projector / shell equality theorems
--
-- These make the projector algebra explicit as named theorems,
-- so that tail_supported, shellOmega_eq_proj, etc. are seen as
-- projector-algebra consequences, not assumptions.
-- ============================================================

/-- [Alg] Shell-projected vorticity equals the projector applied to the
    full vorticity (definitional, exposed as theorem). -/
theorem shellOmega_eq_projector_of_projector_identity
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      shellOmegaLp ns k = ns.projData.Pk k ns.vorticityLp :=
  shellOmegaLp_eq_projector ns

/-- [Alg] Scalar-multiplied shell field equals sigmaLp smul projected vorticity
    (definitional, exposed as theorem). -/
theorem sigmaOmegaLp_eq_projected_smul_of_projector_identity
    {K_max : ℕ}
    (ns : NavierStokesProjectedLpCoreData K_max) :
    ∀ k : Fin K_max,
      sigmaOmegaLp ns k = ns.sigmaLp k • shellOmegaLp ns k :=
  sigmaOmegaLp_eq_smul ns

/-- [Alg] The Lp-level core data preserve the shell-projection identity. -/
theorem shellwise_projector_transport_identity_of_projector_identity
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecLpCoreData K_max) :
    ∀ k : Fin K_max,
      ns.shellOmegaLp k = ns.projData.Pk k ns.vorticityLp :=
  ns.shellOmega_def

/-- [Alg] Each shell projector is contractive in norm. -/
theorem shell_projector_contraction_of_projector_identity
    {K_max : ℕ}
    (spd : ShellProjectorData L2VecT3 K_max) :
    ∀ k : Fin K_max, ∀ z : L2VecT3,
      ‖spd.Pk k z‖ ≤ ‖z‖ :=
  fun k z => (spd.proj_contraction k) z

#check @shellOmega_eq_projector_of_projector_identity
#check @sigmaOmegaLp_eq_projected_smul_of_projector_identity
#check @shellwise_projector_transport_identity_of_projector_identity
#check @shell_projector_contraction_of_projector_identity

end NSProjectorShellEqualityTheorems
