import NSBarrier.NSUnitWidthEuclideanRadius
import Mathlib.Tactic

namespace NSLowShellLocalClosureActual

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandClosure
open NSFiniteBandEnergy
open NSLowShellTriadLocality
open NSTriadGeometryOffset
open NSUnitWidthTriadGeometry
open NSUnitWidthEuclideanRadius

-- ============================================================
-- SECTION 1: ACTUAL UNIT-WIDTH SUPPORT EXCLUSION DATA
-- ============================================================

/-- Actual support-exclusion data coming from the true unit-width Fourier geometry
with Euclidean radius on `Mode = Fin 3 → ℤ`.

The only remaining geometric input is `tail_supported`:
every nonzero tail contribution on shell `k` must arise from a high-low
interaction admissible in the actual unit-width Fourier triad geometry. -/
structure ActualUnitWidthSupportExclusionData (K_max : ℕ) where
  split : LowShellTriadSplit K_max
  Ncut : ℕ
  Nhi : ℕ
  sep : 2 * Ncut + 2 ≤ Nhi

  /-- Any nonzero tail contribution must come from an actual high-low interaction
      in the unit-width Fourier shell geometry. -/
  tail_supported :
    ∀ n : ℕ, ∀ k : Fin K_max, split.P_tail n k ≠ 0 →
      ∃ p q : Fin K_max,
        unitWidthAllowed euclideanRadiusData k p q ∧
        Nhi ≤ p.val ∧
        q.val < Ncut

#check @ActualUnitWidthSupportExclusionData

/-- The actual Euclidean unit-width shell geometry induces the abstract
offset support-exclusion data with offset `C0 = 2`. -/
noncomputable def toHighLowSupportExclusionOffsetData
    {K_max : ℕ}
    (data : ActualUnitWidthSupportExclusionData K_max) :
    HighLowSupportExclusionOffsetData K_max 2 where
  split := data.split
  geom := actualUnitWidthTriadSupportGeometryOffset K_max
  Ncut := data.Ncut
  Nhi := data.Nhi
  sep := data.sep
  tail_supported := data.tail_supported

#check @toHighLowSupportExclusionOffsetData

-- ============================================================
-- SECTION 2: TAIL VANISHING ON LOW SHELLS
-- ============================================================

/-- Therefore the tail part vanishes identically on low output shells. -/
theorem tail_zero_of_actual_unitWidth_support_exclusion
    {K_max : ℕ}
    (data : ActualUnitWidthSupportExclusionData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < data.Ncut → data.split.P_tail n k = 0 := by
  exact
    tail_zero_of_high_low_support_exclusion_offset
      (toHighLowSupportExclusionOffsetData data)

#check @tail_zero_of_actual_unitWidth_support_exclusion

-- ============================================================
-- SECTION 3: ACTUAL LOW-SHELL LOCAL CLOSURE
-- ============================================================

/-- If the local part of the shell production is controlled by a closure function
of the low-shell energy, then the full low-shell production satisfies the same
closure thanks to actual unit-width support exclusion. -/
theorem lowShell_closure_of_actual_unitWidth_geometry
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : ActualUnitWidthSupportExclusionData K_max)
    (F : ℝ → ℝ)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = data.split.P_loc n k + data.split.P_tail n k)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < data.Ncut →
          data.split.P_loc n k
            ≤ F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < data.Ncut →
        (traj n).P k ≤ F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k := by
  exact
    lowShell_closure_of_high_low_support_exclusion_offset
      traj Eshell (toHighLowSupportExclusionOffsetData data) F
      hdecomp hloc

#check @lowShell_closure_of_actual_unitWidth_geometry

-- ============================================================
-- SECTION 4: CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- Actual Euclidean unit-width support exclusion plus local low-shell closure
implies the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_actual_unitWidth_geometry
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : ActualUnitWidthSupportExclusionData K_max)
    (F : ℝ → ℝ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, data.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = data.split.P_loc n k + data.split.P_tail n k)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < data.Ncut →
          data.split.P_loc n k
            ≤ F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) data.Ncut)
            ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ m : ℕ, E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 := by
  exact
    eventual_discrete_gronwall_of_high_low_support_exclusion_offset
      traj E Eshell (toHighLowSupportExclusionOffsetData data) F C
      hC hFmono hFnonneg hEn
      hinc htail hdecomp hloc hDiss hEtot

#check @eventual_discrete_gronwall_of_actual_unitWidth_geometry

/-- Uniform-ratio corollary for the actual Euclidean unit-width shell geometry. -/
theorem eventual_discrete_gronwall_of_uniform_actual_unitWidth_geometry
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : ActualUnitWidthSupportExclusionData K_max)
    (F : ℝ → ℝ)
    (M C : ℝ)
    (hM : 0 ≤ M)
    (hC : 0 ≤ C)
    (hFM : ∀ x : ℝ, 0 ≤ x → F x ≤ M)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, data.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = data.split.P_loc n k + data.split.P_tail n k)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < data.Ncut →
          data.split.P_loc n k
            ≤ F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) data.Ncut)
            ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_high_low_support_exclusion_offset
      traj E Eshell (toHighLowSupportExclusionOffsetData data) F M C
      hM hC hFM hEn
      hinc htail hdecomp hloc hDiss hEtot

#check @eventual_discrete_gronwall_of_uniform_actual_unitWidth_geometry

end NSLowShellLocalClosureActual
