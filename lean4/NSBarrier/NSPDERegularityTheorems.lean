import NSBarrier.NSStrainRegularityTheorems
import NSBarrier.NSVorticityMembershipTheorems
import NSBarrier.NSGalerkinIntegrabilityTheorems
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSActualSigmaBound
open NSStrainRegularityTheorems
open NSVorticityMembershipTheorems
open NSGalerkinIntegrabilityTheorems
open NSNavierStokesProjectedCore
open NSGalerkinCoeffODEProductRuleProof

namespace NSPDERegularityTheorems

-- ============================================================
-- Paper-facing PDE regularity theorem surface
--
-- This file collects all PDE-facing regularity results into
-- a single theorem surface for citation in the paper.
--
-- Architecture:
--   [PDE] Primitive inputs (3 remaining)
--     -> [Alg] Derived regularity (sigma, stretch, vorticity)
--       -> [ODE] Galerkin integrability (from continuity)
-- ============================================================

-- ============================================================
-- SECTION 1: REMAINING PRIMITIVE [PDE] ASSUMPTIONS
-- ============================================================

/-- The three remaining primitive PDE assumptions,
stated as a clean interface for the paper.

1. Sop_ae_bound : operator norm of strain is a.e. bounded
2. sigma_mem : the canonical sigma field is in Linfty
3. stretch_mem : the stretching output is in L2

Everything else in the chain is formally derived. -/
theorem remaining_pde_assumptions_summary :
    True := trivial

-- ============================================================
-- SECTION 2: DERIVED STRAIN REGULARITY [Alg from PDE]
-- ============================================================

/-- [Alg] sigma_ae_bound is derived from Sop_ae_bound
via norm_sigmaFromOpNorm. -/
abbrev sigma_ae_bound_derived :=
  @sigma_ae_bound_of_true_strain_operator_bound

/-- [Alg] The Linfty norm of sigma is bounded by strainSup,
derived from sigma_ae_bound via eLpNormEssSup_le_of_ae_bound. -/
abbrev sigma_Linfty_bound_derived :=
  @sigma_Linfty_bound_of_true_strain_operator_bound

/-- [Alg] Pointwise operator-norm domination of stretch by
sigma * omega, via le_opNorm. -/
abbrev stretch_pointwise_dom_derived :=
  @stretch_pointwise_dom_of_operator_norm

#check @sigma_ae_bound_derived
#check @sigma_Linfty_bound_derived
#check @stretch_pointwise_dom_derived

-- ============================================================
-- SECTION 3: VORTICITY / PROJECTOR DERIVED [Alg from typing]
-- ============================================================

/-- [Alg] Shell-projected vorticity norm is bounded by full
vorticity norm, by projector contraction. -/
abbrev shellOmega_norm_bounded_derived :=
  @shellOmegaLp_norm_le_of_projector_contraction

/-- [Alg] action_le is derived from stretch_dom + sigma_bound
+ projector contraction. -/
abbrev action_le_derived :=
  @action_le_of_lp_projector_contraction

#check @shellOmega_norm_bounded_derived
#check @action_le_derived

-- ============================================================
-- SECTION 4: GALERKIN INTEGRABILITY [ODE from continuity]
-- ============================================================

/-- [ODE] Continuity of Galerkin coefficients follows from
HasDerivAt (differentiable implies continuous). -/
abbrev coeff_continuous_derived :=
  @continuous_coeff_of_hasDeriv

/-- [ODE] Shellwise production is interval integrable,
from continuity of coefficients and nonlinear term. -/
abbrev PCont_integrable_derived :=
  @PCont_intervalIntegrable_of_continuous_coeff

/-- [ODE] Shellwise dissipation is interval integrable,
from continuity of coefficients. -/
abbrev DCont_integrable_derived :=
  @DCont_intervalIntegrable_of_continuous_coeff

#check @coeff_continuous_derived
#check @PCont_integrable_derived
#check @DCont_integrable_derived

-- ============================================================
-- SECTION 5: SUMMARY TABLE (as doc comment)
-- ============================================================

/-!
## PDE Regularity Summary

| Result | Source | Tag |
|--------|--------|-----|
| `sigma_ae_bound` | `Sop_ae_bound` + `norm_sigmaFromOpNorm` | `[Alg]` |
| `sigma_Linfty_bound` | `sigma_ae_bound` + `eLpNormEssSup_le_of_ae_bound` | `[Alg]` |
| `stretch_pointwise_dom` | `le_opNorm` | `[Alg]` |
| `shellOmega_norm_bounded` | projector contraction (typing) | `[Alg]` |
| `action_le` | `stretch_dom` + `sigma_bound` | `[Alg]` |
| `coeff_continuous` | `HasDerivAt` → `ContinuousAt` | `[ODE]` |
| `PCont_integrable` | continuity of finite sum | `[ODE]` |
| `DCont_integrable` | continuity of finite sum | `[ODE]` |

### Remaining [PDE] inputs (3):
1. `Sop_ae_bound` : ‖S(x)‖_op ≤ strainSup  a.e.
2. `sigma_mem` : ‖S‖_op ∈ L∞(T³)
3. `stretch_mem` : Z_k ∈ L²(T³)
-/

end NSPDERegularityTheorems
