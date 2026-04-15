import NSBarrier.NSShellBlockUpperActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSShellBlockModewiseActual

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
open NSShellBlockUpperActual

/-- Canonical shell-block energy sum built from a primitive modewise shell-energy term. -/
noncomputable def shellBlockEnergySum
    {K_max : ℕ}
    (modes : Finset Mode)
    (shellEnergyTerm : ℕ → Mode → ℝ)
    (shellOf : Mode → Fin K_max)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k), shellEnergyTerm n κ

#check @shellBlockEnergySum

/-- Primitive actual modewise shell-block data.

This reduces the remaining Fourier-side input
`hshellBlockUpper_le_shellEnergy`
to two finite-sum steps:

1. `modeWeightSq ≤ shellEnergyTerm` pointwise on active modes;
2. the shellwise sum of `shellEnergyTerm` is bounded by `k² * Eshell`.

Everything downstream is then inherited automatically from
`NSShellBlockUpperActual`.
-/
structure ActualModewiseShellBlockData (K_max : ℕ) where
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

  modes : Finset Mode
  coeffAbs : ℕ → Mode → ℝ
  hcoeffAbs_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ coeffAbs n κ

  shellOf : Mode → Fin K_max

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
  hshellOf_low :
    ∀ κ : Mode, κ ∈ modes → (shellOf κ).val < supportData.Ncut

  hcoeff_partition :
    ∀ n : ℕ,
      ∑ κ ∈ modes, (coeffAbs n κ)^2
        ≤
      ∑ k ∈ lowShells (K_max := K_max) supportData.Ncut,
        shellCoeffSq modes coeffAbs shellOf n k

  modeWeightSq : ℕ → Mode → ℝ
  hmodeWeightSq_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeWeightSq n κ
  hcoeffSq_le_modeWeightSq :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes → (coeffAbs n κ)^2 ≤ modeWeightSq n κ

  /-- Primitive modewise shell-energy term. -/
  shellEnergyTerm : ℕ → Mode → ℝ
  hshellEnergyTerm_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ shellEnergyTerm n κ

  /-- Step 1: pointwise majorization from mode weight to shell-energy term. -/
  hmodeWeightSq_le_shellEnergyTerm :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes → modeWeightSq n κ ≤ shellEnergyTerm n κ

  /-- Step 2: shellwise sum of shell-energy terms is controlled by `k² * Eshell`. -/
  hshellEnergySum_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellBlockEnergySum modes shellEnergyTerm shellOf n k
          ≤
        ((k.val : ℝ)^2) * Eshell n k

#check @ActualModewiseShellBlockData

theorem hshellBlockUpper_le_shellEnergy_of_modewise
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k
          ≤
        ((k.val : ℝ)^2) * ns.Eshell n k := by
  intro n k hk
  have h1 :
      shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k
        ≤
      shellBlockEnergySum ns.modes ns.shellEnergyTerm ns.shellOf n k := by
    unfold shellBlockUpperOfModeWeights shellBlockEnergySum
    refine Finset.sum_le_sum ?_
    intro κ hκ
    exact ns.hmodeWeightSq_le_shellEnergyTerm n κ (Finset.mem_filter.mp hκ).1
  exact le_trans h1 (ns.hshellEnergySum_le_shellEnergy n k hk)

#check @hshellBlockUpper_le_shellEnergy_of_modewise

noncomputable def toActualShellBlockUpperModeData
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ActualShellBlockUpperModeData K_max where
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
  hpairing_Xi := ns.hpairing_Xi
  hP_loc_zero := ns.hP_loc_zero
  modes := ns.modes
  coeffAbs := ns.coeffAbs
  hcoeffAbs_nonneg := ns.hcoeffAbs_nonneg
  shellOf := ns.shellOf
  hshellOf_low := ns.hshellOf_low
  hcoeff_partition := ns.hcoeff_partition
  modeWeightSq := ns.modeWeightSq
  hmodeWeightSq_nonneg := ns.hmodeWeightSq_nonneg
  hcoeffSq_le_modeWeightSq := ns.hcoeffSq_le_modeWeightSq
  hshellBlockUpper_le_shellEnergy := hshellBlockUpper_le_shellEnergy_of_modewise ns

#check @toActualShellBlockUpperModeData

theorem eventual_discrete_gronwall_of_modewiseShellBlock
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_shellBlockUpperMode
      (toActualShellBlockUpperModeData ns)

#check @eventual_discrete_gronwall_of_modewiseShellBlock

end NSShellBlockModewiseActual
