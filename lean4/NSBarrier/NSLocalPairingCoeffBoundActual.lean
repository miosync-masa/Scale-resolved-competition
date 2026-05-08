import NSBarrier.NSLocalPairingXiActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSLocalPairingCoeffBoundActual

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

/-- Canonical shellwise local pairing coefficient obtained by summing
a primitive modewise pairing contribution over the active finite mode set. -/
noncomputable def localPairingCoeffOfTerms
    {K_max : ℕ}
    (modes : Finset Mode)
    (pairTerm : ℕ → Fin K_max → Mode → ℝ)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes, pairTerm n k κ

#check @localPairingCoeffOfTerms

theorem localPairingCoeffOfTerms_nonneg
    {K_max : ℕ}
    (modes : Finset Mode)
    (pairTerm : ℕ → Fin K_max → Mode → ℝ)
    (hpairTerm_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode, 0 ≤ pairTerm n k κ) :
    ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ localPairingCoeffOfTerms modes pairTerm n k := by
  intro n k
  unfold localPairingCoeffOfTerms
  exact Finset.sum_nonneg (by
    intro κ hκ
    exact hpairTerm_nonneg n k κ)

#check @localPairingCoeffOfTerms_nonneg

/-- Primitive actual local-pairing coefficient-bound data.

This reduces the remaining Fourier-side input `hlocalPairingCoeff_le_l1`
to a pointwise modewise majorization
  `pairTerm n k κ ≤ coeffAbs n κ`,
whose finite sum over the active mode set gives the desired shellwise
pairing-coefficient bound.

Everything downstream is then inherited automatically from
`NSLocalPairingXiActual`.
-/
structure ActualLocalPairingTermData (K_max : ℕ) where
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

  Xi : ℕ → Fin K_max → ℝ
  hXi_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Xi n k
  hD_def :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        (traj n).D k = ν * ((k.val : ℝ) ^ 2) * Xi n k

  modes : Finset Mode
  coeffAbs : ℕ → Mode → ℝ
  hcoeffAbs_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ coeffAbs n κ

  shellOf : Mode → Fin K_max
  hshellOf_low :
    ∀ κ : Mode, κ ∈ modes → (shellOf κ).val < supportData.Ncut

  hcoeff_partition :
    ∀ n : ℕ,
      ∑ κ ∈ modes, (coeffAbs n κ)^2
        ≤
      ∑ k ∈ lowShells (K_max := K_max) supportData.Ncut,
        shellCoeffSq modes coeffAbs shellOf n k

  shellBlockUpper : ℕ → Fin K_max → ℝ
  hshellCoeffSq_le_upper :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellCoeffSq modes coeffAbs shellOf n k ≤ shellBlockUpper n k
  hshellBlockUpper_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellBlockUpper n k ≤ ((k.val : ℝ)^2) * Eshell n k

  /-- Primitive modewise local pairing contribution. -/
  pairTerm : ℕ → Fin K_max → Mode → ℝ
  hpairTerm_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode, 0 ≤ pairTerm n k κ

  /-- Pointwise modewise majorization by the canonical coefficient magnitude. -/
  hpairTerm_le_coeffAbs :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ modes → pairTerm n k κ ≤ coeffAbs n κ

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  hpairing_localCoeff :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        supportData.split.P_loc n k
          ≤ localPairingCoeffOfTerms modes pairTerm n k * Xi n k

#check @ActualLocalPairingTermData

/-- Summing the pointwise modewise majorization over the active mode set gives
`localPairingCoeff ≤ l1LocalStrainAmp`. -/
theorem hlocalPairingCoeff_le_l1_of_pairTerms
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < ns.supportData.Ncut →
      1 ≤ k.val →
        localPairingCoeffOfTerms ns.modes ns.pairTerm n k
          ≤
        l1LocalStrainAmp ns.modes ns.coeffAbs n := by
  intro n k hk hk1
  unfold localPairingCoeffOfTerms l1LocalStrainAmp
  refine Finset.sum_le_sum ?_
  intro κ hκ
  exact ns.hpairTerm_le_coeffAbs n k κ hκ

#check @hlocalPairingCoeff_le_l1_of_pairTerms

/-- The primitive actual local-pairing term data induce the previous
`ActualLocalPairingCoeffData`. -/
noncomputable def toActualLocalPairingCoeffData
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max) :
    ActualLocalPairingCoeffData K_max where
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
  shellBlockUpper := ns.shellBlockUpper
  hshellCoeffSq_le_upper := ns.hshellCoeffSq_le_upper
  hshellBlockUpper_le_shellEnergy := ns.hshellBlockUpper_le_shellEnergy
  localPairingCoeff := localPairingCoeffOfTerms ns.modes ns.pairTerm
  hP_loc_zero := ns.hP_loc_zero
  hpairing_localCoeff := ns.hpairing_localCoeff
  hlocalPairingCoeff_le_l1 := hlocalPairingCoeff_le_l1_of_pairTerms ns

#check @toActualLocalPairingCoeffData

/-- Therefore the primitive local-pairing term data already yield the
conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_localPairingTerms
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_localPairingCoeff
      (toActualLocalPairingCoeffData ns)

#check @eventual_discrete_gronwall_of_localPairingTerms

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_localPairingTerms
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_localPairingCoeff
      (toActualLocalPairingCoeffData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_localPairingTerms

end NSLocalPairingCoeffBoundActual
