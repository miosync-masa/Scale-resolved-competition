import NSBarrier.NSTriadGeometryOffset
import NSBarrier.NSTorusShellActual
import Mathlib.Tactic

open NSTorusShellActual
open NSTriadGeometryOffset

namespace NSUnitWidthTriadGeometry

-- ============================================================
-- SECTION 1: UNIT-WIDTH SHELL GEOMETRY ON FOURIER MODES
-- ============================================================

/-- A radius on Fourier modes with the properties needed for the shell-index
triangle estimate:
- nonnegativity
- invariance under negation
- triangle inequality under mode addition.

This is the exact interface needed to instantiate the abstract
`TriadSupportGeometryOffset` with offset `C0 = 2`. -/
structure UnitWidthRadiusData where
  radius : Mode → ℝ
  radius_nonneg : ∀ κ : Mode, 0 ≤ radius κ
  radius_neg : ∀ κ : Mode, radius (-κ) = radius κ
  radius_add_le : ∀ κ₁ κ₂ : Mode, radius (κ₁ + κ₂) ≤ radius κ₁ + radius κ₂

#check @UnitWidthRadiusData

/-- Unit-width shell membership:
    `κ` lies in shell `k` if `k ≤ radius κ < k + 1`. -/
def inUnitWidthShell
    (R : UnitWidthRadiusData)
    (k : ℕ) (κ : Mode) : Prop :=
  (k : ℝ) ≤ R.radius κ ∧ R.radius κ < (k : ℝ) + 1

#check @inUnitWidthShell

/-- Shellwise Fourier-triad admissibility:
    there exist output/input modes `κ = κ₁ + κ₂`
    with the prescribed shell memberships. -/
def unitWidthAllowed
    (R : UnitWidthRadiusData)
    {K_max : ℕ}
    (k p q : Fin K_max) : Prop :=
  ∃ κ κ₁ κ₂ : Mode,
    inUnitWidthShell R k.val κ ∧
    inUnitWidthShell R p.val κ₁ ∧
    inUnitWidthShell R q.val κ₂ ∧
    κ = κ₁ + κ₂

#check @unitWidthAllowed

-- ============================================================
-- SECTION 2: THE +2 SHELL-INDEX TRIANGLE ESTIMATE
-- ============================================================

/-- If `κ = κ₁ + κ₂`, with `κ` in shell `k`, `κ₁` in shell `p`,
    and `κ₂` in shell `q`, then `p ≤ k + q + 2`.

This is the shell-index form of the triangle inequality for unit-width shells. -/
theorem unitWidth_high_le_output_plus_low_offset
    (R : UnitWidthRadiusData)
    {K_max : ℕ}
    {k p q : Fin K_max}
    (hall : unitWidthAllowed R k p q) :
    p.val ≤ k.val + q.val + 2 := by
  rcases hall with ⟨κ, κ₁, κ₂, hk, hp, hq, hsum⟩
  have hκ₁_eq : κ₁ = κ + (-κ₂) := by
    have htmp : κ + (-κ₂) = κ₁ := by
      simp [hsum, add_assoc]
    exact htmp.symm
  have hrad :
      R.radius κ₁ ≤ R.radius κ + R.radius κ₂ := by
    calc
      R.radius κ₁ = R.radius (κ + (-κ₂)) := by simp [hκ₁_eq]
      _ ≤ R.radius κ + R.radius (-κ₂) := R.radius_add_le κ (-κ₂)
      _ = R.radius κ + R.radius κ₂ := by simp [R.radius_neg]
  have hrad_lt :
      R.radius κ₁ < (k.val : ℝ) + (q.val : ℝ) + 2 := by
    linarith [hrad, hk.2, hq.2]
  have hp_lt :
      (p.val : ℝ) < (k.val : ℝ) + (q.val : ℝ) + 2 := by
    exact lt_of_le_of_lt hp.1 hrad_lt
  have hp_nat : p.val < k.val + q.val + 2 := by
    exact_mod_cast hp_lt
  exact Nat.le_of_lt hp_nat

#check @unitWidth_high_le_output_plus_low_offset

-- ============================================================
-- SECTION 3: INSTANTIATION OF THE ABSTRACT OFFSET GEOMETRY
-- ============================================================

/-- The actual unit-width shell geometry on Fourier modes induces an instance of
    `TriadSupportGeometryOffset` with offset `C0 = 2`. -/
def unitWidthTriadSupportGeometryOffset
    (R : UnitWidthRadiusData)
    (K_max : ℕ) :
    TriadSupportGeometryOffset K_max 2 where
  allowed := unitWidthAllowed R
  high_le_output_plus_low_offset := by
    intro k p q hall
    exact unitWidth_high_le_output_plus_low_offset R hall

#check @unitWidthTriadSupportGeometryOffset

-- ============================================================
-- SECTION 4: A SUPPORT-EXCLUSION COROLLARY
-- ============================================================

/-- Therefore the abstract offset support-exclusion theorem applies verbatim
    to the actual unit-width shell geometry. -/
theorem high_low_cannot_project_back_to_low_unitWidth
    (R : UnitWidthRadiusData)
    {K_max : ℕ}
    {Ncut Nhi : ℕ}
    (hsep : 2 * Ncut + 2 ≤ Nhi)
    {k p q : Fin K_max}
    (hk : k.val < Ncut)
    (hq : q.val < Ncut)
    (hp : Nhi ≤ p.val)
    (hall : unitWidthAllowed R k p q) :
    False := by
  exact
    high_low_cannot_project_back_to_low_offset
      (unitWidthTriadSupportGeometryOffset R K_max)
      hsep hk hq hp hall

#check @high_low_cannot_project_back_to_low_unitWidth

end NSUnitWidthTriadGeometry
