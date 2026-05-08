import NSBarrier.NSTorusShellFinite
import NSBarrier.NSAnalyticA2
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open NSTorusShellActual
open NSTorusShellFinite
open NSAnalyticA2

namespace NSTorusShellModes

-- ============================================================
-- SECTION 1: CONCRETE MODE ENUMERATION
-- ============================================================

/-- The three coordinate indices in `Fin 3`. -/
def i0 : Fin 3 := ⟨0, by decide⟩
def i1 : Fin 3 := ⟨1, by decide⟩
def i2 : Fin 3 := ⟨2, by decide⟩

/-- A symmetric integer box `[-R, R]`. -/
noncomputable def coordBox (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

#check @coordBox

/-- Turn a triple of integers into a Fourier mode on `T³`. -/
def modeOfCubeTriple (t : (ℤ × ℤ) × ℤ) : Mode :=
  fun i =>
    if i = i0 then
      t.1.1
    else if i = i1 then
      t.1.2
    else
      t.2

#check @modeOfCubeTriple

/-- A finite cube of Fourier modes. -/
noncomputable def modeCube (R : ℕ) : Finset Mode :=
  (((coordBox R).product (coordBox R)).product (coordBox R)).image modeOfCubeTriple

#check @modeCube

/-- Squared Euclidean size of a Fourier mode, computed on the three coordinates. -/
def modeSqNormZ (κ : Mode) : ℤ :=
  (κ i0) ^ 2 + (κ i1) ^ 2 + (κ i2) ^ 2

#check @modeSqNormZ

-- ============================================================
-- SECTION 2: CONCRETE SHELLS
-- ============================================================

/-- A concrete annular shell:
    k² ≤ |κ|² < (k+1)²,
    enumerated inside the finite cube of radius `k+1`. -/
noncomputable def shellModes {K_max : ℕ} (k : Fin K_max) : Finset Mode :=
  (modeCube (k.val + 1)).filter (fun κ =>
    (((k.val : ℕ) : ℤ) ^ 2 ≤ modeSqNormZ κ) ∧
    (modeSqNormZ κ < (((k.val + 1 : ℕ) : ℤ) ^ 2)))

/-- The resulting concrete mode family. -/
noncomputable def shellModesFamily (K_max : ℕ) : ModeFamily K_max :=
  fun k => shellModes k

#check @shellModes
#check @shellModesFamily

/-- Lower squared-radius bound for a mode in `shellModes k`. -/
theorem modeSqNormZ_lower_of_mem_shellModes
    {K_max : ℕ} {k : Fin K_max} {κ : Mode}
    (hκ : κ ∈ shellModes k) :
    (((k.val : ℕ) : ℤ) ^ 2 ≤ modeSqNormZ κ) := by
  exact (Finset.mem_filter.mp hκ).2.1

/-- Upper squared-radius bound for a mode in `shellModes k`. -/
theorem modeSqNormZ_upper_of_mem_shellModes
    {K_max : ℕ} {k : Fin K_max} {κ : Mode}
    (hκ : κ ∈ shellModes k) :
    modeSqNormZ κ < (((k.val + 1 : ℕ) : ℤ) ^ 2) := by
  exact (Finset.mem_filter.mp hκ).2.2

#check @modeSqNormZ_lower_of_mem_shellModes
#check @modeSqNormZ_upper_of_mem_shellModes

-- ============================================================
-- SECTION 3: ACTUAL SHELL PROJECTOR FAMILY
-- ============================================================

/-- The concrete actual shell projector family on `L²(T³)`. -/
noncomputable def actualShellProjFamily {K_max : ℕ} :
    Fin K_max → (L2T3 →L[ℂ] L2T3) :=
  shellProjFamily' (shellModesFamily K_max)

/-- Each concrete actual shell projector is contractive. -/
theorem actualShellProjFamily_contraction {K_max : ℕ}
    (k : Fin K_max) (f : L2T3) :
    ‖actualShellProjFamily (K_max := K_max) k f‖ ≤ ‖f‖ := by
  exact shellProjFamily'_contraction (shellModesFamily K_max) k f

#check @actualShellProjFamily
#check @actualShellProjFamily_contraction

-- ============================================================
-- SECTION 4: RADIUS PROFILE FOR A2
-- ============================================================

/-- A concrete shell radius-squared profile:
    R²_k := (k+1)². -/
noncomputable def shellRadiusSq {K_max : ℕ} : RadiusSqProfile K_max :=
  fun k => ((k.val : ℝ) + 1) ^ 2

/-- For positive shells, (k+1)² ≤ 4 k². -/
theorem shellRadiusSq_control {K_max : ℕ} :
    RadiusSqControlledByIndex (shellRadiusSq (K_max := K_max)) (4 : ℝ) := by
  intro k hkpos
  unfold shellRadiusSq
  have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hkpos
  nlinarith

#check @shellRadiusSq
#check @shellRadiusSq_control

end NSTorusShellModes
