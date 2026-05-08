import NSBarrier.NSLocalPartActual
import Mathlib.Tactic

namespace NSLocalPartEstimateActual

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
open NSLowShellLocalClosureActual
open NSLocalPartActual

-- ============================================================
-- SECTION 1: LOCAL RATIO ESTIMATE DATA
-- ============================================================

/-- Actual local-part estimate data.

This isolates the final analytic input to the theorem chain in a flexible form:
a time-dependent local ratio `ρ(n)` controls the local production shellwise,
and `ρ(n)` itself is controlled by a closure function of the low-shell energy. -/
structure ActualLocalRatioEstimateData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  F : ℝ → ℝ
  C : ℝ

  hC : 0 ≤ C
  hFmono : Monotone F
  hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x

  /-- Nonnegativity of the shell energies. -/
  hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k

  /-- One-step enstrophy increment is controlled by the total shell net source. -/
  hinc :
    ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ

  /-- High shells are eventually dissipative. -/
  htail :
    ∃ Nt : ℕ,
      ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, supportData.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k

  /-- Actual production split into local and tail parts. -/
  hdecomp :
    ∀ n : ℕ, ∀ k : Fin K_max,
      (traj n).P k =
        supportData.split.P_loc n k + supportData.split.P_tail n k

  /-- Low-shell dissipation is eventually controlled by `C * E(n)`. -/
  hDiss :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (traj n)
          (lowShells (K_max := K_max) supportData.Ncut) ≤ C * E n

  /-- Total shell energy is eventually bounded. -/
  hEtot :
    ∃ Ns : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B

  /-- Time-dependent local ratio. -/
  localRatio : ℕ → ℝ

  /-- The local ratio is controlled by the low-shell energy closure function. -/
  hlocalRatio_bound :
    ∀ n : ℕ,
      localRatio n ≤ F (lowShellEnergy Eshell supportData.Ncut n)

  /-- Shellwise local production is controlled by the local ratio. -/
  hlocalRatio_est :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
        supportData.split.P_loc n k ≤ localRatio n * (traj n).D k

#check @ActualLocalRatioEstimateData

-- ============================================================
-- SECTION 2: THE LOCAL CLOSURE hloc
-- ============================================================

/-- From the local ratio estimate one obtains the desired local closure
    `hloc` used by `NSLocalPartActual`. -/
theorem hloc_of_localRatioEstimate
    {K_max : ℕ}
    (ns : ActualLocalRatioEstimateData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < ns.supportData.Ncut →
        ns.supportData.split.P_loc n k
          ≤ ns.F (lowShellEnergy ns.Eshell ns.supportData.Ncut n) * (ns.traj n).D k := by
  intro n k hk
  have hbase :
      ns.supportData.split.P_loc n k ≤ ns.localRatio n * (ns.traj n).D k :=
    ns.hlocalRatio_est n k hk
  have hmult :
      ns.localRatio n * (ns.traj n).D k
        ≤ ns.F (lowShellEnergy ns.Eshell ns.supportData.Ncut n) * (ns.traj n).D k := by
    exact mul_le_mul_of_nonneg_right
      (ns.hlocalRatio_bound n)
      ((ns.traj n).D_nonneg k)
  exact le_trans hbase hmult

#check @hloc_of_localRatioEstimate

-- ============================================================
-- SECTION 3: BRIDGE TO NSLocalPartActual
-- ============================================================

/-- The local ratio estimate data induce the full actual local-part data
    used by the final conditional Grönwall theorem chain. -/
noncomputable def toActualLocalPartData
    {K_max : ℕ}
    (ns : ActualLocalRatioEstimateData K_max) :
    ActualLocalPartData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  F := ns.F
  C := ns.C
  hC := ns.hC
  hFmono := ns.hFmono
  hFnonneg := ns.hFnonneg
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hloc := hloc_of_localRatioEstimate ns
  hDiss := ns.hDiss
  hEtot := ns.hEtot

#check @toActualLocalPartData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the local ratio estimate already yields the conditional
    discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_localRatioEstimate
    {K_max : ℕ}
    (ns : ActualLocalRatioEstimateData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ns.F B ∧
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + ns.F B * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_true_local_part
      (toActualLocalPartData ns)

#check @eventual_discrete_gronwall_of_localRatioEstimate

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_localRatioEstimate
    {K_max : ℕ}
    (ns : ActualLocalRatioEstimateData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM : ∀ x : ℝ, 0 ≤ x → ns.F x ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_true_local_part
      (toActualLocalPartData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_localRatioEstimate

-- ============================================================
-- SECTION 5: A SIMPLE LINEAR CLOSURE SPECIALIZATION
-- ============================================================

/-- Monotonicity of a linear closure function `x ↦ A * x` for `A ≥ 0`. -/
theorem monotone_mul_nonneg (A : ℝ) (hA : 0 ≤ A) :
    Monotone (fun x : ℝ => A * x) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left hxy hA

/-- Nonnegativity of a linear closure function `x ↦ A * x` for `A ≥ 0`. -/
theorem mul_nonneg_of_nonneg_arg (A : ℝ) (hA : 0 ≤ A) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ A * x := by
  intro x hx
  exact mul_nonneg hA hx

#check @monotone_mul_nonneg
#check @mul_nonneg_of_nonneg_arg

/-- Linear local closure specialization:
    if `ρ(n) ≤ A * E_<N(n)`, then the conditional Grönwall theorem applies
    with `F(x) = A * x`. -/
theorem eventual_discrete_gronwall_of_linear_localRatioEstimate
    {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (E : EnstrophyTrajectory)
    (Eshell : ShellEnergyTrajectory K_max)
    (supportData : ActualUnitWidthSupportExclusionData K_max)
    (A C : ℝ)
    (hA : 0 ≤ A)
    (hC : 0 ≤ C)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k)
    (hinc :
      ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max, supportData.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k)
    (hdecomp :
      ∀ n : ℕ, ∀ k : Fin K_max,
        (traj n).P k =
          supportData.split.P_loc n k + supportData.split.P_tail n k)
    (hDiss :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource (traj n)
            (lowShells (K_max := K_max) supportData.Ncut) ≤ C * E n)
    (hEtot :
      ∃ Ns : ℕ, ∃ B : ℝ,
        ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B)
    (localRatio : ℕ → ℝ)
    (hlocalRatio_bound :
      ∀ n : ℕ,
        localRatio n ≤ A * lowShellEnergy Eshell supportData.Ncut n)
    (hlocalRatio_est :
      ∀ n : ℕ, ∀ k : Fin K_max,
        k.val < supportData.Ncut →
          supportData.split.P_loc n k ≤ localRatio n * (traj n).D k) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ A * B ∧
      ∀ m : ℕ, E (N0 + m) ≤ (1 + (A * B) * C) ^ m * E N0 := by
  let F : ℝ → ℝ := fun x => A * x
  have hFmono : Monotone F := monotone_mul_nonneg A hA
  have hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x := mul_nonneg_of_nonneg_arg A hA
  let ns : ActualLocalRatioEstimateData K_max := {
    traj := traj
    E := E
    Eshell := Eshell
    supportData := supportData
    F := F
    C := C
    hC := hC
    hFmono := hFmono
    hFnonneg := hFnonneg
    hEn := hEn
    hinc := hinc
    htail := htail
    hdecomp := hdecomp
    hDiss := hDiss
    hEtot := hEtot
    localRatio := localRatio
    hlocalRatio_bound := hlocalRatio_bound
    hlocalRatio_est := hlocalRatio_est
  }
  simpa [F] using eventual_discrete_gronwall_of_localRatioEstimate ns

#check @eventual_discrete_gronwall_of_linear_localRatioEstimate

end NSLocalPartEstimateActual
