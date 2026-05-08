import NSBarrier.NSShellBlockModewiseActual
import NSBarrier.NSLocalPairingCoeffBoundActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSLocalPairingModewiseActual

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
open NSFiniteFourierActual
open NSShellBlockCoeffActual
open NSLocalPairingXiActual
open NSShellBlockUpperActual
open NSShellBlockModewiseActual
open NSLocalPairingCoeffBoundActual

/-- Canonical shellwise local production sum built from primitive modewise local
pairing contributions. -/
noncomputable def localProductionOfTerms
    {K_max : ℕ}
    (modes : Finset Mode)
    (localProdTerm : ℕ → Fin K_max → Mode → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes, localProdTerm n k κ

#check @localProductionOfTerms

/-- Primitive modewise actual local-pairing data. -/
structure ActualModewiseLocalPairingData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max
  C : ℝ
  ν : ℝ
  hC : 0 ≤ C
  hν : 0 < ν
  hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k
  hinc : ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ
  htail : ∃ Nt, ∀ n, Nt ≤ n → ∀ k : Fin K_max, supportData.Ncut ≤ k.val →
    (traj n).P k ≤ (traj n).D k
  hdecomp : ∀ n k, (traj n).P k = supportData.split.P_loc n k + supportData.split.P_tail n k
  hDiss : ∃ Nd, ∀ n, Nd ≤ n →
    shellDissipationSource (traj n) (lowShells (K_max := K_max) supportData.Ncut) ≤ C * E n
  hEtot : ∃ Ns, ∃ B, ∀ n, Ns ≤ n → totalShellEnergy Eshell n ≤ B
  Xi : ℕ → Fin K_max → ℝ
  hXi_nonneg : ∀ n k, 0 ≤ Xi n k
  hD_def : ∀ n k, k.val < supportData.Ncut → 1 ≤ k.val →
    (traj n).D k = ν * ((k.val : ℝ) ^ 2) * Xi n k
  modes : Finset Mode
  coeffAbs : ℕ → Mode → ℝ
  hcoeffAbs_nonneg : ∀ n κ, 0 ≤ coeffAbs n κ
  shellOf : Mode → Fin K_max
  hshellOf_low : ∀ κ, κ ∈ modes → (shellOf κ).val < supportData.Ncut
  hcoeff_partition : ∀ n,
    ∑ κ ∈ modes, (coeffAbs n κ)^2 ≤
    ∑ k ∈ lowShells (K_max := K_max) supportData.Ncut, shellCoeffSq modes coeffAbs shellOf n k
  modeWeightSq : ℕ → Mode → ℝ
  hmodeWeightSq_nonneg : ∀ n κ, 0 ≤ modeWeightSq n κ
  hcoeffSq_le_modeWeightSq : ∀ n κ, κ ∈ modes → (coeffAbs n κ)^2 ≤ modeWeightSq n κ
  shellEnergyTerm : ℕ → Mode → ℝ
  hshellEnergyTerm_nonneg : ∀ n κ, 0 ≤ shellEnergyTerm n κ
  hmodeWeightSq_le_shellEnergyTerm : ∀ n κ, κ ∈ modes → modeWeightSq n κ ≤ shellEnergyTerm n κ
  hshellEnergySum_le_shellEnergy : ∀ n k,
    k ∈ lowShells (K_max := K_max) supportData.Ncut →
    shellBlockEnergySum modes shellEnergyTerm shellOf n k ≤ ((k.val : ℝ)^2) * Eshell n k
  pairTerm : ℕ → Fin K_max → Mode → ℝ
  hpairTerm_nonneg : ∀ n k κ, 0 ≤ pairTerm n k κ
  hpairTerm_le_coeffAbs : ∀ n k κ, κ ∈ modes → pairTerm n k κ ≤ coeffAbs n κ
  localProdTerm : ℕ → Fin K_max → Mode → ℝ
  hP_loc_le_sum_localProd : ∀ n k, k.val < supportData.Ncut → 1 ≤ k.val →
    supportData.split.P_loc n k ≤ localProductionOfTerms modes localProdTerm n k
  hlocalProd_le_pairTermXi : ∀ n k κ,
    k.val < supportData.Ncut → 1 ≤ k.val → κ ∈ modes →
    localProdTerm n k κ ≤ pairTerm n k κ * Xi n k
  hP_loc_zero : ∀ n k, k.val = 0 → supportData.split.P_loc n k ≤ 0

#check @ActualModewiseLocalPairingData

theorem hpairing_localCoeff_of_modewiseLocalProd
    {K_max : ℕ}
    (ns : ActualModewiseLocalPairingData K_max) :
    ∀ n k, k.val < ns.supportData.Ncut → 1 ≤ k.val →
      ns.supportData.split.P_loc n k ≤
        localPairingCoeffOfTerms ns.modes ns.pairTerm n k * ns.Xi n k := by
  intro n k hk hk1
  have h1 := ns.hP_loc_le_sum_localProd n k hk hk1
  have h2 : localProductionOfTerms ns.modes ns.localProdTerm n k ≤
      ∑ κ ∈ ns.modes, ns.pairTerm n k κ * ns.Xi n k := by
    unfold localProductionOfTerms
    exact Finset.sum_le_sum (fun κ hκ => ns.hlocalProd_le_pairTermXi n k κ hk hk1 hκ)
  have h3 : (∑ κ ∈ ns.modes, ns.pairTerm n k κ * ns.Xi n k) =
      localPairingCoeffOfTerms ns.modes ns.pairTerm n k * ns.Xi n k := by
    unfold localPairingCoeffOfTerms; rw [Finset.sum_mul]
  exact le_trans h1 (le_trans h2 (by simp [h3]))

#check @hpairing_localCoeff_of_modewiseLocalProd

/-- Derive `hpairing_Xi` from the modewise data (combining local pairing
    coefficient bound with the l1 strain amplitude bound). -/
theorem hpairing_Xi_of_modewiseLocalPairing
    {K_max : ℕ}
    (ns : ActualModewiseLocalPairingData K_max) :
    ∀ n k, k.val < ns.supportData.Ncut → 1 ≤ k.val →
      ns.supportData.split.P_loc n k ≤
        l1LocalStrainAmp ns.modes ns.coeffAbs n * ns.Xi n k := by
  intro n k hk hk1
  have h1 := hpairing_localCoeff_of_modewiseLocalProd ns n k hk hk1
  have h2 : localPairingCoeffOfTerms ns.modes ns.pairTerm n k ≤
      l1LocalStrainAmp ns.modes ns.coeffAbs n := by
    unfold localPairingCoeffOfTerms l1LocalStrainAmp
    exact Finset.sum_le_sum (fun κ hκ => ns.hpairTerm_le_coeffAbs n k κ hκ)
  exact le_trans h1
    (mul_le_mul_of_nonneg_right h2 (ns.hXi_nonneg n k))

#check @hpairing_Xi_of_modewiseLocalPairing

/-- The primitive modewise local-pairing data induce
`ActualLocalPairingTermData`. -/
noncomputable def toActualLocalPairingTermData
    {K_max : ℕ}
    (ns : ActualModewiseLocalPairingData K_max) :
    ActualLocalPairingTermData K_max where
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
  Xi := ns.Xi
  hXi_nonneg := ns.hXi_nonneg
  hD_def := ns.hD_def
  modes := ns.modes
  coeffAbs := ns.coeffAbs
  hcoeffAbs_nonneg := ns.hcoeffAbs_nonneg
  shellOf := ns.shellOf
  hshellOf_low := ns.hshellOf_low
  hcoeff_partition := ns.hcoeff_partition
  shellBlockUpper := fun n k =>
    shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k
  hshellCoeffSq_le_upper := by
    intro n k hk
    unfold shellBlockUpperOfModeWeights shellCoeffSq
    exact Finset.sum_le_sum (fun κ hκ => by
      have hm := Finset.mem_filter.mp hκ
      exact ns.hcoeffSq_le_modeWeightSq n κ
        (Finset.mem_of_mem_filter _ hκ))
  hshellBlockUpper_le_shellEnergy := by
    intro n k hk
    unfold shellBlockUpperOfModeWeights
    calc ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k), ns.modeWeightSq n κ
        ≤ ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k), ns.shellEnergyTerm n κ := by
          exact Finset.sum_le_sum (fun κ hκ =>
            ns.hmodeWeightSq_le_shellEnergyTerm n κ (Finset.mem_of_mem_filter _ hκ))
      _ = shellBlockEnergySum ns.modes ns.shellEnergyTerm ns.shellOf n k := by
          rfl
      _ ≤ ((k.val : ℝ)^2) * ns.Eshell n k :=
          ns.hshellEnergySum_le_shellEnergy n k hk
  pairTerm := ns.pairTerm
  hpairTerm_nonneg := ns.hpairTerm_nonneg
  hpairTerm_le_coeffAbs := ns.hpairTerm_le_coeffAbs
  hP_loc_zero := ns.hP_loc_zero
  hpairing_localCoeff := hpairing_localCoeff_of_modewiseLocalProd ns

#check @toActualLocalPairingTermData

/-- Therefore the primitive modewise local-pairing data already yield the
conditional discrete Gronwall bound. -/
theorem eventual_discrete_gronwall_of_modewiseLocalPairing
    {K_max : ℕ}
    (ns : ActualModewiseLocalPairingData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes *
        (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m) ≤
        (1 + ((((bernsteinConstant ns.modes *
          (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν)
          * ns.C)) ^ m * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_localPairingTerms
      (toActualLocalPairingTermData ns)

#check @eventual_discrete_gronwall_of_modewiseLocalPairing

end NSLocalPairingModewiseActual
