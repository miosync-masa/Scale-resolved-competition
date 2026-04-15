import NSBarrier.NSFiniteFourierActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSShellBlockCoeffActual

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

/-- Primitive shell-block coefficient data.

This reduces the remaining Fourier-side input `hshellCoeffSq_bound`
to a two-step shell-block estimate:

1. `shellCoeffSq ≤ shellBlockUpper`
2. `shellBlockUpper ≤ k² * Eshell`

Everything downstream is then inherited automatically from
`NSFiniteFourierActual`.
-/
structure ActualShellBlockCoeffData (K_max : ℕ) where
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

  /-- Primitive shell-block upper bound. -/
  shellBlockUpper : ℕ → Fin K_max → ℝ

  /-- Step 1: the actual shell coefficient square block is controlled by
      the chosen shell-block upper bound. -/
  hshellCoeffSq_le_upper :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellCoeffSq modes coeffAbs shellOf n k ≤ shellBlockUpper n k

  /-- Step 2: the shell-block upper bound is controlled by the weighted shell energy. -/
  hshellBlockUpper_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        shellBlockUpper n k ≤ ((k.val : ℝ)^2) * Eshell n k

#check @ActualShellBlockCoeffData

/-- Therefore the shell coefficient square block is controlled by the weighted shell energy. -/
theorem hshellCoeffSq_bound_of_upper
    {K_max : ℕ}
    (ns : ActualShellBlockCoeffData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellCoeffSq ns.modes ns.coeffAbs ns.shellOf n k
          ≤
        ((k.val : ℝ)^2) * ns.Eshell n k := by
  intro n k hk
  exact le_trans
    (ns.hshellCoeffSq_le_upper n k hk)
    (ns.hshellBlockUpper_le_shellEnergy n k hk)

#check @hshellCoeffSq_bound_of_upper

/-- The primitive shell-block coefficient data induce the previous
    `ActualFiniteFourierModeData`. -/
noncomputable def toActualFiniteFourierModeData
    {K_max : ℕ}
    (ns : ActualShellBlockCoeffData K_max) :
    ActualFiniteFourierModeData K_max where
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
  hshellCoeffSq_bound := hshellCoeffSq_bound_of_upper ns

#check @toActualFiniteFourierModeData

/-- Therefore the primitive shell-block coefficient data already yield the
conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_shellBlockCoeff
    {K_max : ℕ}
    (ns : ActualShellBlockCoeffData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_actualFiniteFourier
      (toActualFiniteFourierModeData ns)

#check @eventual_discrete_gronwall_of_shellBlockCoeff

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_shellBlockCoeff
    {K_max : ℕ}
    (ns : ActualShellBlockCoeffData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_actualFiniteFourier
      (toActualFiniteFourierModeData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_shellBlockCoeff

end NSShellBlockCoeffActual
