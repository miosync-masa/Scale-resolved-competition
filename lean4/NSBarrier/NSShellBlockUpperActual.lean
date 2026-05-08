import NSBarrier.NSShellBlockCoeffActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSShellBlockUpperActual

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

/-- Canonical shell-block upper bound obtained by summing a primitive nonnegative
modewise majorant over the shell block. -/
noncomputable def shellBlockUpperOfModeWeights
    {K_max : ℕ}
    (modes : Finset Mode)
    (modeWeightSq : ℕ → Mode → ℝ)
    (shellOf : Mode → Fin K_max)
    (n : ℕ) (k : Fin K_max) : ℝ :=
  ∑ κ ∈ modes.filter (fun κ => shellOf κ = k), modeWeightSq n κ

#check @shellBlockUpperOfModeWeights

/-- Primitive actual shell-block upper-bound data.

This reduces the remaining Fourier-side input `hshellCoeffSq_le_upper`
to a pointwise modewise majorization
  `(coeffAbs n κ)^2 ≤ modeWeightSq n κ`,
whose finite sum over a shell block gives the desired shell-block upper bound.

Everything downstream is then inherited automatically from
`NSShellBlockCoeffActual`.
-/
structure ActualShellBlockUpperModeData (K_max : ℕ) where
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

  /-- Primitive nonnegative modewise upper weight. -/
  modeWeightSq : ℕ → Mode → ℝ
  hmodeWeightSq_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeWeightSq n κ

  /-- Pointwise majorization of the coefficient square. -/
  hcoeffSq_le_modeWeightSq :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes → (coeffAbs n κ)^2 ≤ modeWeightSq n κ

  /-- The shell-block upper bound built from `modeWeightSq` is controlled by
      the weighted shell energy. -/
  hshellBlockUpper_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellBlockUpperOfModeWeights modes modeWeightSq shellOf n k
          ≤
        ((k.val : ℝ)^2) * Eshell n k

#check @ActualShellBlockUpperModeData

/-- Summing the pointwise modewise majorization over a shell block gives
`shellCoeffSq ≤ shellBlockUpper`. -/
theorem hshellCoeffSq_le_shellBlockUpper_of_modeWeights
    {K_max : ℕ}
    (ns : ActualShellBlockUpperModeData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellCoeffSq ns.modes ns.coeffAbs ns.shellOf n k
          ≤
        shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k := by
  intro n k hk
  unfold shellCoeffSq shellBlockUpperOfModeWeights
  refine Finset.sum_le_sum ?_
  intro κ hκ
  exact ns.hcoeffSq_le_modeWeightSq n κ (Finset.mem_filter.mp hκ).1

#check @hshellCoeffSq_le_shellBlockUpper_of_modeWeights

/-- The primitive actual shell-block upper-bound data induce the previous
`ActualShellBlockCoeffData`. -/
noncomputable def toActualShellBlockCoeffData
    {K_max : ℕ}
    (ns : ActualShellBlockUpperModeData K_max) :
    ActualShellBlockCoeffData K_max where
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
  shellBlockUpper := shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf
  hshellCoeffSq_le_upper := hshellCoeffSq_le_shellBlockUpper_of_modeWeights ns
  hshellBlockUpper_le_shellEnergy := ns.hshellBlockUpper_le_shellEnergy

#check @toActualShellBlockCoeffData

/-- Therefore the primitive actual shell-block upper-bound data already yield the
conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_shellBlockUpperMode
    {K_max : ℕ}
    (ns : ActualShellBlockUpperModeData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_shellBlockCoeff
      (toActualShellBlockCoeffData ns)

#check @eventual_discrete_gronwall_of_shellBlockUpperMode

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_shellBlockUpperMode
    {K_max : ℕ}
    (ns : ActualShellBlockUpperModeData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_shellBlockCoeff
      (toActualShellBlockCoeffData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_shellBlockUpperMode

end NSShellBlockUpperActual
