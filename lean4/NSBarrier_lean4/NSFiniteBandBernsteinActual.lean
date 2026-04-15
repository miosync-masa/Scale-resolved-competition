import NSBarrier.NSLocalPairingToDissipation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace NSFiniteBandBernsteinActual

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
open NSLocalPartEstimateActual
open NSFiniteBandSobolevBridge
open NSLocalPairingToDissipation

-- ============================================================
-- SECTION 1: THE sqrt-CLOSURE FUNCTION
-- ============================================================

/-- The canonical finite-band Bernstein closure function. -/
noncomputable def sqrtClosure (A : ℝ) : ℝ → ℝ :=
  fun x => A * Real.sqrt x

theorem monotone_sqrtClosure
    (A : ℝ) (hA : 0 ≤ A) :
    Monotone (sqrtClosure A) := by
  intro x y hxy
  unfold sqrtClosure
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) hA

theorem nonneg_sqrtClosure
    (A : ℝ) (hA : 0 ≤ A) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ sqrtClosure A x := by
  intro x hx
  unfold sqrtClosure
  exact mul_nonneg hA (Real.sqrt_nonneg x)

#check @sqrtClosure
#check @monotone_sqrtClosure
#check @nonneg_sqrtClosure

-- ============================================================
-- SECTION 2: ACTUAL FINITE-BAND BERNSTEIN DATA
-- ============================================================

/-- Actual finite-band Bernstein data.

This is the final pre-analytic bridge:
all theorem architecture below is complete once one can supply
the estimate
  `localStrainAmp(n) ≤ A * sqrt(E_<N(n))`.

At that point, the whole conditional Grönwall chain follows automatically. -/
structure ActualFiniteBandBernsteinXiData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  C : ℝ
  ν : ℝ
  A : ℝ

  hC : 0 ≤ C
  hν : 0 < ν
  hA : 0 ≤ A

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

  /-- Effective local strain amplitude. -/
  localStrainAmp : ℕ → ℝ
  hlocalStrain_nonneg : ∀ n : ℕ, 0 ≤ localStrainAmp n

  /-- The shellwise quadratic quantity entering the local pairing estimate. -/
  Xi : ℕ → Fin K_max → ℝ
  hXi_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Xi n k

  /-- Dissipation is `ν k² Xi_k` on low shells `k ≥ 1`. -/
  hD_def :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        (traj n).D k = ν * ((k.val : ℝ) ^ 2) * Xi n k

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  /-- Local pairing bound with `Xi`. -/
  hpairing_Xi :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        supportData.split.P_loc n k ≤ localStrainAmp n * Xi n k

  /-- The actual finite-band Bernstein / Sobolev estimate. -/
  hlocalStrain_sqrt :
    ∀ n : ℕ,
      localStrainAmp n ≤ A * Real.sqrt (lowShellEnergy Eshell supportData.Ncut n)

#check @ActualFiniteBandBernsteinXiData

-- ============================================================
-- SECTION 3: BRIDGE TO THE LOCAL-PAIRING/Xi FRAMEWORK
-- ============================================================

/-- The finite-band Bernstein data induce the general local-pairing/Xi data
    with closure function `x ↦ A * sqrt(x)`. -/
noncomputable def toActualLocalPairingXiData
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinXiData K_max) :
    ActualLocalPairingXiData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  F := sqrtClosure ns.A
  C := ns.C
  ν := ns.ν
  hC := ns.hC
  hν := ns.hν
  hFmono := monotone_sqrtClosure ns.A ns.hA
  hFnonneg := nonneg_sqrtClosure ns.A ns.hA
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localStrainAmp := ns.localStrainAmp
  hlocalStrain_nonneg := ns.hlocalStrain_nonneg
  Xi := ns.Xi
  hXi_nonneg := ns.hXi_nonneg
  hD_def := ns.hD_def
  hpairing_Xi := ns.hpairing_Xi
  hP_loc_zero := ns.hP_loc_zero
  hlocalStrain_bound := by
    intro n
    simpa [sqrtClosure] using ns.hlocalStrain_sqrt n

#check @toActualLocalPairingXiData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the actual finite-band Bernstein estimate already yields
    the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_finiteBandBernsteinXi
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinXiData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ns.A * Real.sqrt B / ns.ν ∧
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + (ns.A * Real.sqrt B / ns.ν) * ns.C) ^ m * ns.E N0 := by
  simpa [sqrtClosure] using
    eventual_discrete_gronwall_of_localPairingXi
      (toActualLocalPairingXiData ns)

#check @eventual_discrete_gronwall_of_finiteBandBernsteinXi

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_finiteBandBernsteinXi
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinXiData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x → ns.A * Real.sqrt x / ns.ν ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  simpa [sqrtClosure] using
    eventual_discrete_gronwall_of_uniform_localPairingXi
      (toActualLocalPairingXiData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_finiteBandBernsteinXi

end NSFiniteBandBernsteinActual
