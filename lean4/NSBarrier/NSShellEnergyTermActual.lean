import NSBarrier.NSShellBlockModewiseActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSShellEnergyTermActual

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
open NSShellBlockModewiseActual

/-- Canonical modewise shell-energy term:
    shell factor times modewise energy coefficient. -/
noncomputable def shellEnergyTermOfModeEnergy
    (shellFactor : Mode → ℝ)
    (modeEnergyCoeff : ℕ → Mode → ℝ)
    (n : ℕ) (κ : Mode) : ℝ :=
  shellFactor κ * modeEnergyCoeff n κ

#check @shellEnergyTermOfModeEnergy

theorem shellEnergyTermOfModeEnergy_nonneg
    (shellFactor : Mode → ℝ)
    (modeEnergyCoeff : ℕ → Mode → ℝ)
    (hshellFactor_nonneg : ∀ κ : Mode, 0 ≤ shellFactor κ)
    (hmodeEnergyCoeff_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeEnergyCoeff n κ) :
    ∀ n : ℕ, ∀ κ : Mode, 0 ≤ shellEnergyTermOfModeEnergy shellFactor modeEnergyCoeff n κ := by
  intro n κ
  unfold shellEnergyTermOfModeEnergy
  exact mul_nonneg (hshellFactor_nonneg κ) (hmodeEnergyCoeff_nonneg n κ)

#check @shellEnergyTermOfModeEnergy_nonneg

/-- Primitive actual modewise shell-energy data.

This reduces the remaining Fourier-side input
`hshellEnergySum_le_shellEnergy`
to two genuinely modewise ingredients:

1. a shell factor `shellFactor κ` that is bounded by `k²` on shell `k`;
2. a modewise energy coefficient whose shellwise sum is controlled by `E_k`.

Everything downstream is then inherited automatically from
`NSShellBlockModewiseActual`.
-/
structure ActualModewiseShellEnergyData (K_max : ℕ) where
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

  /-- Primitive shell factor. -/
  shellFactor : Mode → ℝ
  hshellFactor_nonneg : ∀ κ : Mode, 0 ≤ shellFactor κ

  /-- On the shell block indexed by `k`, the shell factor is bounded by `k²`. -/
  hshellFactor_le_on_block :
    ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ modes →
      shellOf κ = k →
        shellFactor κ ≤ ((k.val : ℝ) ^ 2)

  /-- Primitive modewise shell-energy coefficient. -/
  modeEnergyCoeff : ℕ → Mode → ℝ
  hmodeEnergyCoeff_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeEnergyCoeff n κ

  /-- Pointwise majorization from mode weight to shell-energy term. -/
  hmodeWeightSq_le_shellEnergyTerm :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes →
        modeWeightSq n κ
          ≤
        shellEnergyTermOfModeEnergy shellFactor modeEnergyCoeff n κ

  /-- Shellwise sum of the modewise energy coefficients is controlled by `E_k`. -/
  hmodeEnergyCoeff_sum_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        ∑ κ ∈ modes.filter (fun κ => shellOf κ = k), modeEnergyCoeff n κ
          ≤
        Eshell n k

#check @ActualModewiseShellEnergyData

theorem hshellEnergySum_le_shellEnergy_of_modeEnergy
    {K_max : ℕ}
    (ns : ActualModewiseShellEnergyData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellBlockEnergySum ns.modes
          (shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff)
          ns.shellOf n k
          ≤
        ((k.val : ℝ)^2) * ns.Eshell n k := by
  intro n k hk
  have h1 :
      shellBlockEnergySum ns.modes
        (shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff)
        ns.shellOf n k
        ≤
      ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k),
        ((k.val : ℝ)^2) * ns.modeEnergyCoeff n κ := by
    unfold shellBlockEnergySum shellEnergyTermOfModeEnergy
    refine Finset.sum_le_sum ?_
    intro κ hκ
    have hm : κ ∈ ns.modes := (Finset.mem_filter.mp hκ).1
    have hs : ns.shellOf κ = k := (Finset.mem_filter.mp hκ).2
    have hsf : ns.shellFactor κ ≤ ((k.val : ℝ)^2) :=
      ns.hshellFactor_le_on_block k κ hm hs
    exact mul_le_mul_of_nonneg_right hsf (ns.hmodeEnergyCoeff_nonneg n κ)
  have h2 :
      (∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k),
        ((k.val : ℝ)^2) * ns.modeEnergyCoeff n κ)
        =
      ((k.val : ℝ)^2) *
        ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k), ns.modeEnergyCoeff n κ := by
    rw [Finset.mul_sum]
  have h3 :
      ((k.val : ℝ)^2) *
        ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k), ns.modeEnergyCoeff n κ
        ≤
      ((k.val : ℝ)^2) * ns.Eshell n k := by
    exact mul_le_mul_of_nonneg_left
      (ns.hmodeEnergyCoeff_sum_le_shellEnergy n k hk)
      (sq_nonneg (k.val : ℝ))
  calc
    shellBlockEnergySum ns.modes
      (shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff)
      ns.shellOf n k
      ≤
    ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k),
      ((k.val : ℝ)^2) * ns.modeEnergyCoeff n κ := h1
    _ =
    ((k.val : ℝ)^2) *
      ∑ κ ∈ ns.modes.filter (fun κ => ns.shellOf κ = k), ns.modeEnergyCoeff n κ := h2
    _ ≤ ((k.val : ℝ)^2) * ns.Eshell n k := h3

#check @hshellEnergySum_le_shellEnergy_of_modeEnergy

noncomputable def toActualModewiseShellBlockData
    {K_max : ℕ}
    (ns : ActualModewiseShellEnergyData K_max) :
    ActualModewiseShellBlockData K_max where
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
  shellEnergyTerm := shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff
  hshellEnergyTerm_nonneg :=
    shellEnergyTermOfModeEnergy_nonneg
      ns.shellFactor ns.modeEnergyCoeff
      ns.hshellFactor_nonneg ns.hmodeEnergyCoeff_nonneg
  hmodeWeightSq_le_shellEnergyTerm := ns.hmodeWeightSq_le_shellEnergyTerm
  hshellEnergySum_le_shellEnergy := hshellEnergySum_le_shellEnergy_of_modeEnergy ns

#check @toActualModewiseShellBlockData

theorem eventual_discrete_gronwall_of_modewiseShellEnergy
    {K_max : ℕ}
    (ns : ActualModewiseShellEnergyData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_modewiseShellBlock
      (toActualModewiseShellBlockData ns)

#check @eventual_discrete_gronwall_of_modewiseShellEnergy

end NSShellEnergyTermActual
