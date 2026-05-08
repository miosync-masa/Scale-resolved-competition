import NSBarrier.NSFiniteFourierBernstein
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open NSTorusShellActual

namespace NSFiniteFourierActual

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
open NSFiniteBandBernsteinProof
open NSLocalH1EnergyBound
open NSFiniteFourierBernstein

-- ============================================================
-- SECTION 1: CANONICAL FINITE-FOURIER DEFINITIONS
-- ============================================================

/-- Canonical finite-Fourier ℓ¹ strain amplitude. -/
noncomputable def l1LocalStrainAmp
    (modes : Finset Mode)
    (coeffAbs : ℕ → Mode → ℝ)
    (n : ℕ) : ℝ :=
  ∑ κ ∈ modes, coeffAbs n κ

/-- Shellwise coefficient block energy on the finite active mode set. -/
noncomputable def shellCoeffSq
    {K_max : ℕ}
    (modes : Finset Mode)
    (coeffAbs : ℕ → Mode → ℝ)
    (shellOf : Mode → Fin K_max)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k), (coeffAbs n κ)^2

#check @l1LocalStrainAmp
#check @shellCoeffSq

theorem l1LocalStrainAmp_nonneg
    (modes : Finset Mode)
    (coeffAbs : ℕ → Mode → ℝ)
    (hcoeffAbs_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ coeffAbs n κ) :
    ∀ n : ℕ, 0 ≤ l1LocalStrainAmp modes coeffAbs n := by
  intro n
  unfold l1LocalStrainAmp
  exact Finset.sum_nonneg (by
    intro κ hκ
    exact hcoeffAbs_nonneg n κ)

theorem shellCoeffSq_nonneg
    {K_max : ℕ}
    (modes : Finset Mode)
    (coeffAbs : ℕ → Mode → ℝ)
    (shellOf : Mode → Fin K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ shellCoeffSq modes coeffAbs shellOf n k := by
  intro n k
  unfold shellCoeffSq
  exact Finset.sum_nonneg (by
    intro κ hκ
    exact sq_nonneg (coeffAbs n κ))

#check @l1LocalStrainAmp_nonneg
#check @shellCoeffSq_nonneg

-- ============================================================
-- SECTION 2: ACTUAL FINITE-FOURIER DATA
-- ============================================================

/-- Actual finite-Fourier data where the two Bernstein assumptions are replaced by
more primitive shell-block data.

`hcoeff_partition` says that the total coefficient ℓ² mass is controlled by the sum
of its shell blocks.

`hshellCoeffSq_bound` says that each shell block is controlled by the corresponding
weighted shell energy.  From these, `hcoeff_l2_to_localH1` is derived automatically. -/
structure ActualFiniteFourierModeData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  C : ℝ
  ν : ℝ

  hC : 0 ≤ C
  hν : 0 < ν

  hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k
  hinc :
    ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ
  htail :
    ∃ Nt : ℕ,
      ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, supportData.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k
  hdecomp :
    ∀ n : ℕ, ∀ k : Fin K_max,
      (traj n).P k =
        supportData.split.P_loc n k + supportData.split.P_tail n k
  hDiss :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (traj n)
          (lowShells (K_max := K_max) supportData.Ncut) ≤ C * E n
  hEtot :
    ∃ Ns : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B

  /-- Finite active mode set. -/
  modes : Finset Mode

  /-- Absolute coefficient size of the local finite Fourier representation. -/
  coeffAbs : ℕ → Mode → ℝ
  hcoeffAbs_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ coeffAbs n κ

  Xi : ℕ → Fin K_max → ℝ
  hXi_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Xi n k
  hD_def :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        (traj n).D k = ν * ((k.val : ℝ) ^ 2) * Xi n k
  hpairing_Xi :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        supportData.split.P_loc n k
          ≤ l1LocalStrainAmp modes coeffAbs n * Xi n k

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  /-- Assignment of each active mode to a shell. -/
  shellOf : Mode → Fin K_max

  /-- Every active mode belongs to a low shell. -/
  hshellOf_low :
    ∀ κ : Mode, κ ∈ modes → (shellOf κ).val < supportData.Ncut

  /-- Total coefficient ℓ² mass is controlled by the sum of shell blocks. -/
  hcoeff_partition :
    ∀ n : ℕ,
      ∑ κ ∈ modes, (coeffAbs n κ)^2
        ≤
      ∑ k ∈ lowShells (K_max := K_max) supportData.Ncut,
        shellCoeffSq modes coeffAbs shellOf n k

  /-- Each shell block is controlled by the corresponding weighted shell energy. -/
  hshellCoeffSq_bound :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellCoeffSq modes coeffAbs shellOf n k
          ≤
        ((k.val : ℝ)^2) * Eshell n k

#check @ActualFiniteFourierModeData

-- ============================================================
-- SECTION 3: THE TWO BERNSTEIN ASSUMPTIONS, NOW PROVED
-- ============================================================

/-- The ℓ¹ strain-amplitude assumption is now definitional. -/
theorem hlocalStrain_l1_of_definition
    {K_max : ℕ}
    (ns : ActualFiniteFourierModeData K_max) :
    ∀ n : ℕ,
      l1LocalStrainAmp ns.modes ns.coeffAbs n
        ≤
      ∑ κ ∈ ns.modes, ns.coeffAbs n κ := by
  intro n
  unfold l1LocalStrainAmp
  exact le_rfl

#check @hlocalStrain_l1_of_definition

/-- The coefficient ℓ² bound is derived from shell-block control and the
canonical low-shell H¹ energy. -/
theorem hcoeff_l2_to_localH1_of_shellBlocks
    {K_max : ℕ}
    (ns : ActualFiniteFourierModeData K_max) :
    ∀ n : ℕ,
      ∑ κ ∈ ns.modes, (ns.coeffAbs n κ)^2
        ≤
      (localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
  intro n
  have h1 :
      ∑ κ ∈ ns.modes, (ns.coeffAbs n κ)^2
        ≤
      ∑ k ∈ lowShells (K_max := K_max) ns.supportData.Ncut,
        shellCoeffSq ns.modes ns.coeffAbs ns.shellOf n k :=
    ns.hcoeff_partition n
  have h2 :
      ∑ k ∈ lowShells (K_max := K_max) ns.supportData.Ncut,
        shellCoeffSq ns.modes ns.coeffAbs ns.shellOf n k
        ≤
      ∑ k ∈ lowShells (K_max := K_max) ns.supportData.Ncut,
        ((k.val : ℝ)^2) * ns.Eshell n k := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact ns.hshellCoeffSq_bound n k hk
  have h3 :
      ∑ k ∈ lowShells (K_max := K_max) ns.supportData.Ncut,
        ((k.val : ℝ)^2) * ns.Eshell n k
        =
      (localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
    unfold localH1Energy
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun k _ =>
      mul_nonneg (sq_nonneg (k.val : ℝ)) (ns.hEn n k)))]
  exact le_trans h1 (le_trans h2 (by simp [h3]))

#check @hcoeff_l2_to_localH1_of_shellBlocks

-- ============================================================
-- SECTION 4: BRIDGE TO NSFiniteFourierBernstein
-- ============================================================

/-- The primitive actual finite-Fourier data induce the previous
`ActualFiniteFourierBernsteinData`. -/
noncomputable def toActualFiniteFourierBernsteinData
    {K_max : ℕ}
    (ns : ActualFiniteFourierModeData K_max) :
    ActualFiniteFourierBernsteinData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  C := ns.C
  ν := ns.ν
  hC := ns.hC
  hν := ns.hν
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localStrainAmp := l1LocalStrainAmp ns.modes ns.coeffAbs
  hlocalStrain_nonneg := l1LocalStrainAmp_nonneg ns.modes ns.coeffAbs ns.hcoeffAbs_nonneg
  Xi := ns.Xi
  hXi_nonneg := ns.hXi_nonneg
  hD_def := ns.hD_def
  hpairing_Xi := ns.hpairing_Xi
  hP_loc_zero := ns.hP_loc_zero
  modes := ns.modes
  coeffAbs := ns.coeffAbs
  hcoeffAbs_nonneg := ns.hcoeffAbs_nonneg
  hlocalStrain_l1 := by
    intro n
    exact hlocalStrain_l1_of_definition ns n
  hcoeff_l2_to_localH1 := by
    intro n
    exact hcoeff_l2_to_localH1_of_shellBlocks ns n

#check @toActualFiniteFourierBernsteinData

-- ============================================================
-- SECTION 5: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the primitive actual finite-Fourier data already yield the
conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_actualFiniteFourier
    {K_max : ℕ}
    (ns : ActualFiniteFourierModeData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_finiteFourierBernstein
      (toActualFiniteFourierBernsteinData ns)

#check @eventual_discrete_gronwall_of_actualFiniteFourier

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_actualFiniteFourier
    {K_max : ℕ}
    (ns : ActualFiniteFourierModeData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_finiteFourierBernstein
      (toActualFiniteFourierBernsteinData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_actualFiniteFourier

end NSFiniteFourierActual
