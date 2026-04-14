import NSBarrier.NSFiniteBandBernsteinActual
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace NSFiniteBandBernsteinProof

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
open NSFiniteBandBernsteinActual

-- ============================================================
-- SECTION 1: TWO-STEP FINITE-BAND BERNSTEIN PROOF DATA
-- ============================================================

/-- The final actual Fourier-analytic proof data, split into two transparent steps:

1. finite-band Bernstein / Sobolev:
     localStrainAmp ≤ A_bern * localH1
2. low-shell H¹-energy control:
     localH1 ≤ A_h1 * sqrt(E_<N)

Together these yield the desired estimate
     localStrainAmp ≤ (A_bern * A_h1) * sqrt(E_<N),
which is exactly the last missing input of `NSFiniteBandBernsteinActual`.
-/
structure ActualFiniteBandBernsteinProofData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  C : ℝ
  ν : ℝ
  A_bern : ℝ
  A_h1 : ℝ

  hC : 0 ≤ C
  hν : 0 < ν
  hA_bern : 0 ≤ A_bern
  hA_h1 : 0 ≤ A_h1

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

  /-- Auxiliary finite-band H¹-type control quantity. -/
  localH1 : ℕ → ℝ
  hlocalH1_nonneg : ∀ n : ℕ, 0 ≤ localH1 n

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

  /-- Step 1: finite-band Bernstein / Sobolev estimate. -/
  hstrain_to_H1 :
    ∀ n : ℕ,
      localStrainAmp n ≤ A_bern * localH1 n

  /-- Step 2: low-shell H¹ is controlled by the square root of the low-shell energy. -/
  hH1_to_energy :
    ∀ n : ℕ,
      localH1 n ≤ A_h1 * Real.sqrt (lowShellEnergy Eshell supportData.Ncut n)

#check @ActualFiniteBandBernsteinProofData

-- ============================================================
-- SECTION 2: THE LAST ANALYTIC INEQUALITY
-- ============================================================

/-- Combining the finite-band Bernstein estimate with the low-shell H¹-energy bound
gives the desired square-root closure for the local strain amplitude. -/
theorem localStrain_sqrt_of_two_step
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinProofData K_max) :
    ∀ n : ℕ,
      ns.localStrainAmp n
        ≤
      (ns.A_bern * ns.A_h1) * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n) := by
  intro n
  have h1 :
      ns.localStrainAmp n ≤ ns.A_bern * ns.localH1 n :=
    ns.hstrain_to_H1 n
  have h2 :
      ns.localH1 n ≤ ns.A_h1 * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n) :=
    ns.hH1_to_energy n
  have h3 :
      ns.A_bern * ns.localH1 n
        ≤
      ns.A_bern * (ns.A_h1 * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n)) := by
    exact mul_le_mul_of_nonneg_left h2 ns.hA_bern
  calc
    ns.localStrainAmp n ≤ ns.A_bern * ns.localH1 n := h1
    _ ≤ ns.A_bern * (ns.A_h1 * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n)) := h3
    _ = (ns.A_bern * ns.A_h1) * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n) := by
        ring

#check @localStrain_sqrt_of_two_step

-- ============================================================
-- SECTION 3: BRIDGE TO NSFiniteBandBernsteinActual
-- ============================================================

/-- The two-step Bernstein proof data induce the previous
`ActualFiniteBandBernsteinXiData` with `A = A_bern * A_h1`. -/
noncomputable def toActualFiniteBandBernsteinXiData
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinProofData K_max) :
    ActualFiniteBandBernsteinXiData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  C := ns.C
  ν := ns.ν
  A := ns.A_bern * ns.A_h1
  hC := ns.hC
  hν := ns.hν
  hA := mul_nonneg ns.hA_bern ns.hA_h1
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
  hlocalStrain_sqrt := localStrain_sqrt_of_two_step ns

#check @toActualFiniteBandBernsteinXiData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the two-step actual Fourier-analytic proof data already yield
the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_finiteBandBernsteinProof
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinProofData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((ns.A_bern * ns.A_h1) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + (((ns.A_bern * ns.A_h1) * Real.sqrt B) / ns.ν) * ns.C) ^ m * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_finiteBandBernsteinXi
      (toActualFiniteBandBernsteinXiData ns)

#check @eventual_discrete_gronwall_of_finiteBandBernsteinProof

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_finiteBandBernsteinProof
    {K_max : ℕ}
    (ns : ActualFiniteBandBernsteinProofData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        ((ns.A_bern * ns.A_h1) * Real.sqrt x) / ns.ν ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_finiteBandBernsteinXi
      (toActualFiniteBandBernsteinXiData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_finiteBandBernsteinProof

end NSFiniteBandBernsteinProof
