import NSBarrier.NSFourier
import NSBarrier.NSAnalyticA1Pairing
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic

open NSFourier
open NSAnalyticA1Pairing
open scoped InnerProductSpace

namespace NSTorusShell

/-- The 3-dimensional torus, written as `(ℝ / ℤ)^3`. -/
abbrev T3 := UnitAddTorus (Fin 3)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- ============================================================
-- SECTION 1: SHELL PROJECTOR FAMILIES
-- ============================================================

/-- A shell projector family on a Hilbert space.
    In the intended application, `V = L²(T³)^3`. -/
structure ShellProjectorData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  Pk : Fin K_max → (V →ₗ[ℝ] V)
  proj_contraction : ∀ k, ProjectionContraction (Pk k)

#check @ShellProjectorData

/-- Each shell projector is contractive in norm. -/
theorem shellProj_apply_norm_le
    {K_max : ℕ}
    (spd : ShellProjectorData V K_max)
    (k : Fin K_max) (z : V) :
    ‖spd.Pk k z‖ ≤ ‖z‖ := by
  exact spd.proj_contraction k z

#check @shellProj_apply_norm_le

-- ============================================================
-- SECTION 2: PAIRING BOUNDS THROUGH THE PROJECTOR FAMILY
-- ============================================================

/-- Pairing bound through a shell projector family:
    |⟪ω_k, P_k Z_k⟫| ≤ ‖ω_k‖ · ‖Z_k‖. -/
theorem shell_pairing_bound_of_projector
    {K_max : ℕ}
    (spd : ShellProjectorData V K_max)
    (omega Z : Fin K_max → V) :
    ∀ k : Fin K_max,
      |⟪omega k, spd.Pk k (Z k)⟫_ℝ| ≤ ‖omega k‖ * ‖Z k‖ := by
  intro k
  exact
    shell_production_pairing_bound_of_contraction
      (spd.Pk k)
      (spd.proj_contraction k)
      (omega k)
      (Z k)

#check @shell_pairing_bound_of_projector

/-- Localized shell production bound through a shell projector family:
    if ‖Z_k‖ ≤ G · ‖ω_k‖, then |⟪ω_k, P_k Z_k⟫| ≤ G · ‖ω_k‖². -/
theorem localized_shell_production_bound_of_projector
    {K_max : ℕ}
    (spd : ShellProjectorData V K_max)
    (omega Z : Fin K_max → V)
    (G : ℝ)
    (hG : ∀ k : Fin K_max, ‖Z k‖ ≤ G * ‖omega k‖) :
    ∀ k : Fin K_max,
      |⟪omega k, spd.Pk k (Z k)⟫_ℝ| ≤ G * ‖omega k‖ ^ 2 := by
  intro k
  exact
    localized_shell_production_bound_of_contraction
      (spd.Pk k)
      (spd.proj_contraction k)
      (omega k)
      (Z k)
      (hG k)

#check @localized_shell_production_bound_of_projector

end NSTorusShell
