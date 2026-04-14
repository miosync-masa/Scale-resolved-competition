import NSBarrier.NSFiniteBandEnergy
import Mathlib.Tactic

namespace NSLowShellTriadLocality

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandClosure
open NSFiniteBandEnergy

-- ============================================================
-- SECTION 1: STRICT TRIAD LOCALITY AS A PRODUCTION SPLIT
-- ============================================================

/-- A shellwise production split into a local part and a tail part. -/
structure LowShellTriadSplit (K_max : ℕ) where
  P_loc : ℕ → Fin K_max → ℝ
  P_tail : ℕ → Fin K_max → ℝ

#check @LowShellTriadSplit

/-- **LOW-SHELL CLOSURE OF STRICT TRIAD LOCALITY**:
    if the shell production splits as `P = P_loc + P_tail`,
    the tail part vanishes identically on low shells,
    and the local part is controlled by a closure function of the low-shell energy,
    then the full low-shell production satisfies the same closure. -/
theorem lowShell_closure_of_strict_triad_locality
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Eshell : ShellEnergyTrajectory K_max)
    (split : LowShellTriadSplit K_max)
    (F : ℝ → ℝ)
    (Ncut : ℕ)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = split.P_loc n k + split.P_tail n k)
    (htail_zero :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut → split.P_tail n k = 0)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut →
          split.P_loc n k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < Ncut →
        (traj n).P k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k := by
  intro n k hk
  rw [hdecomp n k, htail_zero n k hk, add_zero]
  exact hloc n k hk

#check @lowShell_closure_of_strict_triad_locality

-- ============================================================
-- SECTION 2: TRIAD LOCALITY => CONDITIONAL DISCRETE GRONWALL
-- ============================================================

/-- If strict low-shell triad locality holds, then the finite-band energy
    conditional Grönwall theorem applies. -/
theorem eventual_discrete_gronwall_of_strict_triad_locality
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (split : LowShellTriadSplit K_max)
    (F : ℝ → ℝ)
    (C : ℝ) (Ncut : ℕ)
    (hC : 0 ≤ C)
    (hFmono : Monotone F)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = split.P_loc n k + split.P_tail n k)
    (htail_zero :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut → split.P_tail n k = 0)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut →
          split.P_loc n k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ F B ∧
      ∀ m : ℕ, E (N0 + m) ≤ (1 + F B * C) ^ m * E N0 := by
  apply eventual_discrete_gronwall_of_lowShellEnergy_closure
    traj E Eshell F C Ncut
    hC hFmono hFnonneg hEn hinc htail
  · exact lowShell_closure_of_strict_triad_locality
      traj Eshell split F Ncut hdecomp htail_zero hloc
  · exact hDiss
  · exact hEtot

#check @eventual_discrete_gronwall_of_strict_triad_locality

-- ============================================================
-- SECTION 3: A FIXED-RATIO COROLLARY
-- ============================================================

/-- If the local closure function is uniformly bounded by `M` on the relevant
    energy range, then strict triad locality yields the fixed-ratio
    discrete Grönwall theorem. -/
theorem eventual_discrete_gronwall_of_uniform_strict_triad_locality
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (split : LowShellTriadSplit K_max)
    (F : ℝ → ℝ)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hC : 0 ≤ C)
    (hFM : ∀ x : ℝ, 0 ≤ x → F x ≤ M)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k = split.P_loc n k + split.P_tail n k)
    (htail_zero :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut → split.P_tail n k = 0)
    (hloc :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < Ncut →
          split.P_loc n k ≤ F (lowShellEnergy Eshell Ncut n) * (traj n).D k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n) (lowShells (K_max := K_max) Ncut) ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, E (N0 + m) ≤ (1 + M * C) ^ m * E N0 := by
  apply eventual_discrete_gronwall_of_uniform_lowShellEnergy_ratio
    traj E Eshell F M C Ncut
    hM hC hFM hEn hinc htail
  · exact lowShell_closure_of_strict_triad_locality
      traj Eshell split F Ncut hdecomp htail_zero hloc
  · exact hDiss
  · exact hEtot

#check @eventual_discrete_gronwall_of_uniform_strict_triad_locality

end NSLowShellTriadLocality
