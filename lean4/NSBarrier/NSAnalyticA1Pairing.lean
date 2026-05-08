import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# NSAnalyticA1Pairing

Abstract pairing layer for the A1 shell-local production estimate.

This file isolates the part of A1 that only uses Hilbert-space inequalities:
Cauchy-Schwarz and (optionally) contraction of the shell projector.
The genuinely Fourier-analytic shell-local estimate should be added later
in a separate locality file.
-/

open scoped InnerProductSpace

namespace NSAnalyticA1Pairing

/-- A linear map is a contraction in norm. -/
def ProjectionContraction
    {V : Type _}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Pk : V →ₗ[ℝ] V) : Prop :=
  ∀ z, ‖Pk z‖ ≤ ‖z‖

/-- Shell-local projected stretching estimate:
    the projected stretching term is bounded by `G * ‖ω_k‖`. -/
def LocalizedProjectedStretchEstimate
    {V : Type _}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Pk : V →ₗ[ℝ] V)
    (ωk Z : V)
    (G : ℝ) : Prop :=
  ‖Pk Z‖ ≤ G * ‖ωk‖

/-- Pure pairing bound from Cauchy-Schwarz:
    `|⟪ω_k, P_k Z⟫| ≤ ‖ω_k‖ ‖P_k Z‖`. -/
theorem shell_production_pairing_bound
    {V : Type _}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Pk : V →ₗ[ℝ] V)
    (ωk Z : V) :
    ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ ‖ωk‖ * ‖Pk Z‖ := by
  exact norm_inner_le_norm ωk (Pk Z)

/-- Pairing bound plus contraction of the shell projector. -/
theorem shell_production_pairing_bound_of_contraction
    {V : Type _}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Pk : V →ₗ[ℝ] V)
    (hPk : ProjectionContraction Pk)
    (ωk Z : V) :
    ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ ‖ωk‖ * ‖Z‖ := by
  have hpair : ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ ‖ωk‖ * ‖Pk Z‖ :=
    shell_production_pairing_bound Pk ωk Z
  have hmult : ‖ωk‖ * ‖Pk Z‖ ≤ ‖ωk‖ * ‖Z‖ := by
    exact mul_le_mul_of_nonneg_left (hPk Z) (norm_nonneg ωk)
  exact le_trans hpair hmult

/-- Pairing bound plus a shell-local projected stretch estimate.
    This is the abstract `P_k ≤ G Ξ_k` step with `Ξ_k = ‖ω_k‖²`. -/
theorem localized_shell_production_bound
    {V : Type _}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Pk : V →ₗ[ℝ] V)
    (ωk Z : V)
    {G : ℝ}
    (hlocal : LocalizedProjectedStretchEstimate Pk ωk Z G) :
    ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ G * ‖ωk‖ ^ 2 := by
  have hpair : ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ ‖ωk‖ * ‖Pk Z‖ :=
    shell_production_pairing_bound Pk ωk Z
  have hmult : ‖ωk‖ * ‖Pk Z‖ ≤ ‖ωk‖ * (G * ‖ωk‖) := by
    exact mul_le_mul_of_nonneg_left hlocal (norm_nonneg ωk)
  calc
    ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ ‖ωk‖ * ‖Pk Z‖ := hpair
    _ ≤ ‖ωk‖ * (G * ‖ωk‖) := hmult
    _ = G * ‖ωk‖ ^ 2 := by ring

/-- Contraction version: it is enough to bound `‖Z‖` by `G ‖ω_k‖`. -/
theorem localized_shell_production_bound_of_contraction
    {V : Type _}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Pk : V →ₗ[ℝ] V)
    (hPk : ProjectionContraction Pk)
    (ωk Z : V)
    {G : ℝ}
    (hlocal : ‖Z‖ ≤ G * ‖ωk‖) :
    ‖⟪ωk, Pk Z⟫_ℝ‖ ≤ G * ‖ωk‖ ^ 2 := by
  have hPkZ : LocalizedProjectedStretchEstimate Pk ωk Z G :=
    le_trans (hPk Z) hlocal
  exact localized_shell_production_bound Pk ωk Z hPkZ

#check @ProjectionContraction
#check @LocalizedProjectedStretchEstimate
#check @shell_production_pairing_bound
#check @shell_production_pairing_bound_of_contraction
#check @localized_shell_production_bound
#check @localized_shell_production_bound_of_contraction

end NSAnalyticA1Pairing
