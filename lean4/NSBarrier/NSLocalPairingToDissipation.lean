import NSBarrier.NSFiniteBandSobolevBridge
import Mathlib.Tactic

namespace NSLocalPairingToDissipation

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

-- ============================================================
-- SECTION 1: LOCAL PAIRING WITH A VORTICITY-ENERGY DENSITY Xi
-- ============================================================

/-- Actual local pairing data with a shellwise vorticity-energy density `Xi`.

Interpretation:
- `Xi n k` is the shellwise quadratic quantity for the local part
  (typically shell enstrophy / shell vorticity square);
- `D_k = ν k² Xi_k`;
- `P_loc(k) ≤ localStrainAmp(n) * Xi_k`.

From this, on low shells `k ≥ 1`, one gets the ratio form
  `P_loc(k) ≤ (localStrainAmp(n)/ν) * D_k`.
-/
structure ActualLocalPairingXiData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  F : ℝ → ℝ
  C : ℝ
  ν : ℝ

  hC : 0 ≤ C
  hν : 0 < ν
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

  /-- Local pairing bound with `Xi`. -/
  hpairing_Xi :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        supportData.split.P_loc n k ≤ localStrainAmp n * Xi n k

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  /-- Finite-band Sobolev / Bernstein control of the local strain amplitude. -/
  hlocalStrain_bound :
    ∀ n : ℕ,
      localStrainAmp n ≤ F (lowShellEnergy Eshell supportData.Ncut n)

#check @ActualLocalPairingXiData

-- ============================================================
-- SECTION 2: PAIRING + DISSIPATION => LOCAL RATIO
-- ============================================================

/-- On low shells `k ≥ 1`, the local pairing bound and the concrete dissipation
    formula imply a shellwise local-ratio estimate with coefficient
    `localStrainAmp(n) / ν`. -/
theorem hpairing_D_of_pairing_Xi
    {K_max : ℕ}
    (ns : ActualLocalPairingXiData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < ns.supportData.Ncut →
      1 ≤ k.val →
        ns.supportData.split.P_loc n k
          ≤ (ns.localStrainAmp n / ns.ν) * (ns.traj n).D k := by
  intro n k hk hk1
  have hk1r : (1 : ℝ) ≤ (k.val : ℝ) ^ 2 := by
    have hk1r' : (1 : ℝ) ≤ (k.val : ℝ) := by
      exact_mod_cast hk1
    nlinarith
  have hpair :
      ns.supportData.split.P_loc n k ≤ ns.localStrainAmp n * ns.Xi n k :=
    ns.hpairing_Xi n k hk hk1
  have hD :
      (ns.traj n).D k = ns.ν * ((k.val : ℝ) ^ 2) * ns.Xi n k :=
    ns.hD_def n k hk hk1
  have hA : 0 ≤ ns.localStrainAmp n := ns.hlocalStrain_nonneg n
  have hXi : 0 ≤ ns.Xi n k := ns.hXi_nonneg n k
  have hν_ne : ns.ν ≠ 0 := ne_of_gt ns.hν
  have hgoal : ns.localStrainAmp n / ns.ν * (ns.traj n).D k
      = ns.localStrainAmp n * ((k.val : ℝ) ^ 2) * ns.Xi n k := by
    rw [hD]; field_simp
  linarith [mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hXi hk1r) hA]

#check @hpairing_D_of_pairing_Xi

-- ============================================================
-- SECTION 3: BRIDGE TO NSFiniteBandSobolevBridge
-- ============================================================

/-- Monotonicity is preserved under division by a positive constant. -/
theorem monotone_div_pos
    (F : ℝ → ℝ) (ν : ℝ)
    (hFmono : Monotone F)
    (hν : 0 < ν) :
    Monotone (fun x : ℝ => F x / ν) := by
  intro x y hxy
  exact div_le_div_of_nonneg_right (hFmono hxy) (le_of_lt hν)

/-- Nonnegativity is preserved under division by a positive constant. -/
theorem div_nonneg_of_nonneg_arg
    (F : ℝ → ℝ) (ν : ℝ)
    (hν : 0 < ν)
    (hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ F x / ν := by
  intro x hx
  exact div_nonneg (hFnonneg x hx) (le_of_lt hν)

#check @monotone_div_pos
#check @div_nonneg_of_nonneg_arg

/-- The pairing/`Xi` data induce the finite-band Sobolev bridge data,
    with closure function `x ↦ F(x) / ν`. -/
noncomputable def toActualFiniteBandSobolevBridgeData
    {K_max : ℕ}
    (ns : ActualLocalPairingXiData K_max) :
    ActualFiniteBandSobolevBridgeData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  F := fun x => ns.F x / ns.ν
  C := ns.C
  hC := ns.hC
  hFmono := monotone_div_pos ns.F ns.ν ns.hFmono ns.hν
  hFnonneg := div_nonneg_of_nonneg_arg ns.F ns.ν ns.hν ns.hFnonneg
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localStrainAmp := fun n => ns.localStrainAmp n / ns.ν
  hlocalStrain_bound := by
    intro n
    exact div_le_div_of_nonneg_right
      (ns.hlocalStrain_bound n)
      (le_of_lt ns.hν)
  hpairing := by
    intro n k hk
    by_cases hk1 : 1 ≤ k.val
    · exact hpairing_D_of_pairing_Xi ns n k hk hk1
    · have hk0 : k.val = 0 := by omega
      exact le_trans (ns.hP_loc_zero n k hk0)
        (mul_nonneg (div_nonneg (ns.hlocalStrain_nonneg n) (le_of_lt ns.hν))
          ((ns.traj n).D_nonneg k))

#check @toActualFiniteBandSobolevBridgeData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the local pairing + dissipation identity already yield the
    conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_localPairingXi
    {K_max : ℕ}
    (ns : ActualLocalPairingXiData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ns.F B / ns.ν ∧
      ∀ m : ℕ, ns.E (N0 + m) ≤
        (1 + (ns.F B / ns.ν) * ns.C) ^ m * ns.E N0 := by
  exact eventual_discrete_gronwall_of_finiteBandSobolevBridge
    (toActualFiniteBandSobolevBridgeData ns)

#check @eventual_discrete_gronwall_of_localPairingXi

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_localPairingXi
    {K_max : ℕ}
    (ns : ActualLocalPairingXiData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM : ∀ x : ℝ, 0 ≤ x → ns.F x / ns.ν ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_finiteBandSobolevBridge
      (toActualFiniteBandSobolevBridgeData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_localPairingXi

end NSLocalPairingToDissipation
