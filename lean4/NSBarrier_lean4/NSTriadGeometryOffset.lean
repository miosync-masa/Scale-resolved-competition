import NSBarrier.NSLowShellTriadLocality
import Mathlib.Tactic

namespace NSTriadGeometryOffset

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandClosure
open NSFiniteBandEnergy
open NSLowShellTriadLocality

-- ============================================================
-- SECTION 1: TRIAD SUPPORT GEOMETRY WITH AN OFFSET
-- ============================================================

/-- Abstract support geometry for shell interactions, allowing a fixed shell-index
offset `C0` in the triangle estimate.

`allowed k p q` means that an interaction between shells `p` and `q`
can contribute to the output shell `k`.

The only structural axiom we need is:
a high input shell `p` cannot exceed `k + q + C0`
if it contributes to `k` through interaction with `q`. -/
structure TriadSupportGeometryOffset (K_max C0 : ℕ) where
  allowed : Fin K_max → Fin K_max → Fin K_max → Prop
  high_le_output_plus_low_offset :
    ∀ {k p q : Fin K_max}, allowed k p q → p.val ≤ k.val + q.val + C0

#check @TriadSupportGeometryOffset

/-- **HIGH × LOW CANNOT PROJECT BACK TO LOW (OFFSET VERSION)**:
    if the high shell begins above `Nhi`, the low shell is below `Ncut`,
    and the output shell is also below `Ncut`, then no such interaction is allowed
    once `2 * Ncut + C0 ≤ Nhi`. -/
theorem high_low_cannot_project_back_to_low_offset
    {K_max C0 : ℕ}
    (geom : TriadSupportGeometryOffset K_max C0)
    {Ncut Nhi : ℕ}
    (hsep : 2 * Ncut + C0 ≤ Nhi)
    {k p q : Fin K_max}
    (hk : k.val < Ncut)
    (hq : q.val < Ncut)
    (hp : Nhi ≤ p.val)
    (hall : geom.allowed k p q) :
    False := by
  have hp_le : p.val ≤ k.val + q.val + C0 :=
    geom.high_le_output_plus_low_offset hall
  omega

#check @high_low_cannot_project_back_to_low_offset

-- ============================================================
-- SECTION 2: OFFSET SUPPORT EXCLUSION DATA
-- ============================================================

/-- Data saying that every nonzero tail contribution on shell `k`
comes from a high-low interaction, with a spectral gap large enough
to force support exclusion on low output shells, up to the offset `C0`. -/
structure HighLowSupportExclusionOffsetData (K_max C0 : ℕ) where
  split : LowShellTriadSplit K_max
  geom : TriadSupportGeometryOffset K_max C0
  Ncut : ℕ
  Nhi : ℕ
  sep : 2 * Ncut + C0 ≤ Nhi

  /-- Any nonzero tail contribution must come from a high-low interaction. -/
  tail_supported :
    ∀ n : ℕ, ∀ k : Fin K_max, split.P_tail n k ≠ 0 →
      ∃ p q : Fin K_max,
        geom.allowed k p q ∧
        Nhi ≤ p.val ∧
        q.val < Ncut

#check @HighLowSupportExclusionOffsetData

/-- Therefore the tail part vanishes identically on low output shells. -/
theorem tail_zero_of_high_low_support_exclusion_offset
    {K_max C0 : ℕ}
    (data : HighLowSupportExclusionOffsetData K_max C0) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < data.Ncut → data.split.P_tail n k = 0 := by
  intro n k hk
  by_contra hne
  rcases data.tail_supported n k hne with ⟨p, q, hall, hp, hq⟩
  exact high_low_cannot_project_back_to_low_offset
    data.geom data.sep hk hq hp hall

#check @tail_zero_of_high_low_support_exclusion_offset

-- ============================================================
-- SECTION 3: LOW-SHELL CLOSURE FROM OFFSET SUPPORT EXCLUSION
-- ============================================================

/-- If the tail part is excluded from low output shells by support geometry
with offset `C0`, then the full low-shell production is controlled by the
local part alone. -/
theorem lowShell_closure_of_high_low_support_exclusion_offset
    {K_max C0 : ℕ}
    (traj : BudgetTrajectory K_max)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : HighLowSupportExclusionOffsetData K_max C0)
    (F : ℝ → ℝ)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = data.split.P_loc n k + data.split.P_tail n k)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < data.Ncut →
          data.split.P_loc n k ≤
            F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < data.Ncut →
        (traj n).P k ≤ F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k := by
  exact
    lowShell_closure_of_strict_triad_locality
      traj Eshell data.split F data.Ncut
      hdecomp
      (tail_zero_of_high_low_support_exclusion_offset data)
      hloc

#check @lowShell_closure_of_high_low_support_exclusion_offset

-- ============================================================
-- SECTION 4: CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- Offset support exclusion plus local low-shell closure implies the conditional
discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_high_low_support_exclusion_offset
    {K_max C0 : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : HighLowSupportExclusionOffsetData K_max C0)
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
          data.split.P_loc n k ≤
            F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k)
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
    eventual_discrete_gronwall_of_lowShellEnergy_closure
      traj E Eshell F C data.Ncut
      hC hFmono hFnonneg hEn
      hinc htail
      (lowShell_closure_of_high_low_support_exclusion_offset
        traj Eshell data F hdecomp hloc)
      hDiss hEtot

#check @eventual_discrete_gronwall_of_high_low_support_exclusion_offset

/-- Uniform-ratio corollary with offset support exclusion. -/
theorem eventual_discrete_gronwall_of_uniform_high_low_support_exclusion_offset
    {K_max C0 : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (data : HighLowSupportExclusionOffsetData K_max C0)
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
          data.split.P_loc n k ≤
            F (lowShellEnergy Eshell data.Ncut n) * (traj n).D k)
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
    eventual_discrete_gronwall_of_uniform_lowShellEnergy_ratio
      traj E Eshell F M C data.Ncut
      hM hC hFM hEn
      hinc htail
      (lowShell_closure_of_high_low_support_exclusion_offset
        traj Eshell data F hdecomp hloc)
      hDiss hEtot

#check @eventual_discrete_gronwall_of_uniform_high_low_support_exclusion_offset

end NSTriadGeometryOffset
