import NSBarrier.NSLocalPartEstimateActual
import Mathlib.Tactic

namespace NSFiniteBandSobolevBridge

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

-- ============================================================
-- SECTION 1: FINITE-BAND SOBOLEV / BERNSTEIN BRIDGE DATA
-- ============================================================

/-- Data for bridging a finite-band Sobolev/Bernstein estimate into the
`localRatio` framework of `NSLocalPartEstimateActual`.

Interpretation:
- `localStrainAmp n` is the effective local strain amplitude at time `n`
  coming from the finite-band local part;
- `hlocalStrain_bound` is the actual Sobolev/Bernstein-type estimate
  `localStrainAmp(n) ≤ F(E_<N(n))`;
- `hpairing` is the shellwise local pairing bound
  `P_loc(k) ≤ localStrainAmp(n) * D_k`.
-/
structure ActualFiniteBandSobolevBridgeData (K_max : ℕ) where
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

  /-- Effective local strain amplitude. -/
  localStrainAmp : ℕ → ℝ

  /-- Finite-band Sobolev / Bernstein bridge:
      the local strain amplitude is controlled by the low-shell energy. -/
  hlocalStrain_bound :
    ∀ n : ℕ,
      localStrainAmp n ≤ F (lowShellEnergy Eshell supportData.Ncut n)

  /-- Shellwise local pairing bound. -/
  hpairing :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
        supportData.split.P_loc n k ≤ localStrainAmp n * (traj n).D k

#check @ActualFiniteBandSobolevBridgeData

-- ============================================================
-- SECTION 2: BRIDGE TO THE LOCAL-RATIO FRAMEWORK
-- ============================================================

/-- The finite-band Sobolev/Bernstein bridge data induce the local-ratio data
    used by `NSLocalPartEstimateActual`. -/
noncomputable def toActualLocalRatioEstimateData
    {K_max : ℕ}
    (ns : ActualFiniteBandSobolevBridgeData K_max) :
    ActualLocalRatioEstimateData K_max where
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
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localRatio := ns.localStrainAmp
  hlocalRatio_bound := ns.hlocalStrain_bound
  hlocalRatio_est := ns.hpairing

#check @toActualLocalRatioEstimateData

-- ============================================================
-- SECTION 3: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the finite-band Sobolev/Bernstein bridge already yields
    the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_finiteBandSobolevBridge
    {K_max : ℕ}
    (ns : ActualFiniteBandSobolevBridgeData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ns.F B ∧
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + ns.F B * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_localRatioEstimate
      (toActualLocalRatioEstimateData ns)

#check @eventual_discrete_gronwall_of_finiteBandSobolevBridge

/-- Uniform-ratio corollary:
    if the closure function `F` is uniformly bounded by `M`
    on the relevant energy range, then one gets a fixed-ratio exponential bound. -/
theorem eventual_discrete_gronwall_of_uniform_finiteBandSobolevBridge
    {K_max : ℕ}
    (ns : ActualFiniteBandSobolevBridgeData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM : ∀ x : ℝ, 0 ≤ x → ns.F x ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_localRatioEstimate
      (toActualLocalRatioEstimateData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_finiteBandSobolevBridge

end NSFiniteBandSobolevBridge
