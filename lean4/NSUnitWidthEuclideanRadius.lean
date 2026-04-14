import NSBarrier.NSUnitWidthTriadGeometry
import Mathlib.Tactic

open NSTorusShellActual
open NSTriadGeometryOffset
open NSUnitWidthTriadGeometry

namespace NSUnitWidthEuclideanRadius

/-- The real-valued embedding of a Fourier mode `κ : Fin 3 → ℤ`
    into `ℝ^3`. -/
def realMode (κ : Mode) : Fin 3 → ℝ :=
  fun i => (κ i : ℝ)

#check @realMode

/-- The actual Euclidean radius on Fourier modes, obtained by viewing
    `κ : Fin 3 → ℤ` as a vector in `ℝ^3` and taking its norm. -/
noncomputable def euclideanRadiusData : UnitWidthRadiusData where
  radius := fun κ => ‖realMode κ‖
  radius_nonneg := by
    intro κ
    exact norm_nonneg (realMode κ)
  radius_neg := by
    intro κ
    have hreal_neg : realMode (-κ) = - realMode κ := by
      funext i
      simp [realMode]
    rw [hreal_neg]
    exact norm_neg (realMode κ)
  radius_add_le := by
    intro κ₁ κ₂
    have hreal_add : realMode (κ₁ + κ₂) = realMode κ₁ + realMode κ₂ := by
      funext i
      simp [realMode]
    rw [hreal_add]
    exact norm_add_le (realMode κ₁) (realMode κ₂)

#check @euclideanRadiusData

/-- The actual unit-width Fourier shell geometry on `Mode = Fin 3 → ℤ`,
    using the Euclidean norm. -/
noncomputable def actualUnitWidthTriadSupportGeometryOffset
    (K_max : ℕ) :
    TriadSupportGeometryOffset K_max 2 :=
  unitWidthTriadSupportGeometryOffset euclideanRadiusData K_max

#check @actualUnitWidthTriadSupportGeometryOffset

/-- Final actual support-exclusion corollary for unit-width shells
    defined using the Euclidean norm on Fourier modes. -/
theorem actual_high_low_cannot_project_back_to_low
    {K_max : ℕ}
    {Ncut Nhi : ℕ}
    (hsep : 2 * Ncut + 2 ≤ Nhi)
    {k p q : Fin K_max}
    (hk : k.val < Ncut)
    (hq : q.val < Ncut)
    (hp : Nhi ≤ p.val)
    (hall : unitWidthAllowed euclideanRadiusData k p q) :
    False := by
  exact
    high_low_cannot_project_back_to_low_unitWidth
      euclideanRadiusData hsep hk hq hp hall

#check @actual_high_low_cannot_project_back_to_low

end NSUnitWidthEuclideanRadius
