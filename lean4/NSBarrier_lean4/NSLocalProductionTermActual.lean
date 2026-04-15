import NSBarrier.NSLocalPairingModewiseActual
import NSBarrier.NSShellEnergyTermActual
import Mathlib.Tactic

namespace NSLocalProductionTermActual

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
open NSShellEnergyTermActual
open NSLocalPairingXiActual
open NSLocalPairingCoeffBoundActual
open NSLocalPairingModewiseActual

/-- Canonical modewise local production term:
    a modewise local production coefficient times the shellwise quadratic quantity `Xi_k`. -/
noncomputable def localProdTermOfCoeff
    {K_max : ℕ}
    (Xi : ℕ → Fin K_max → ℝ)
    (localProdCoeff : ℕ → Fin K_max → Mode → ℝ)
    (n : ℕ) (k : Fin K_max) (κ : Mode) : ℝ :=
  localProdCoeff n k κ * Xi n k

#check @localProdTermOfCoeff

theorem localProdTermOfCoeff_nonneg
    {K_max : ℕ}
    (Xi : ℕ → Fin K_max → ℝ)
    (localProdCoeff : ℕ → Fin K_max → Mode → ℝ)
    (hXi_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Xi n k)
    (hlocalProdCoeff_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode, 0 ≤ localProdCoeff n k κ) :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      0 ≤ localProdTermOfCoeff Xi localProdCoeff n k κ := by
  intro n k κ
  unfold localProdTermOfCoeff
  exact mul_nonneg (hlocalProdCoeff_nonneg n k κ) (hXi_nonneg n k)

#check @localProdTermOfCoeff_nonneg

/-- Primitive actual modewise local production-coefficient data.

This is the most primitive finite-Fourier local-production layer:
- `P_loc(k)` is controlled by a finite sum of modewise terms `b_{n,k,κ} * Xi_k`
- each `b_{n,k,κ}` is bounded by the canonical coefficient magnitude `coeffAbs(n,κ)`.

Everything downstream is then inherited automatically from
`NSLocalPairingModewiseActual`.
-/
structure ActualModewiseLocalProductionCoeffData (K_max : ℕ) where
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
      ∑ κ in modes, (coeffAbs n κ)^2
        ≤
      ∑ k in lowShells (K_max := K_max) supportData.Ncut,
        shellCoeffSq modes coeffAbs shellOf n k

  modeWeightSq : ℕ → Mode → ℝ
  hmodeWeightSq_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeWeightSq n κ
  hcoeffSq_le_modeWeightSq :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes → (coeffAbs n κ)^2 ≤ modeWeightSq n κ

  shellFactor : Mode → ℝ
  hshellFactor_nonneg : ∀ κ : Mode, 0 ≤ shellFactor κ
  hshellFactor_le_on_block :
    ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ modes →
      shellOf κ = k →
        shellFactor κ ≤ ((k.val : ℝ) ^ 2)

  modeEnergyCoeff : ℕ → Mode → ℝ
  hmodeEnergyCoeff_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ modeEnergyCoeff n κ
  hmodeWeightSq_le_shellEnergyTerm :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ modes →
        modeWeightSq n κ
          ≤
        shellEnergyTermOfModeEnergy shellFactor modeEnergyCoeff n κ
  hmodeEnergyCoeff_sum_le_shellEnergy :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) supportData.Ncut →
        ∑ κ in modes.filter (fun κ => shellOf κ = k), modeEnergyCoeff n κ
          ≤
        Eshell n k

  /-- Primitive modewise local production coefficient. -/
  localProdCoeff : ℕ → Fin K_max → Mode → ℝ
  hlocalProdCoeff_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode, 0 ≤ localProdCoeff n k κ

  /-- Pointwise majorization of the primitive local production coefficient
      by the canonical coefficient magnitude. -/
  hlocalProdCoeff_le_coeffAbs :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ modes → localProdCoeff n k κ ≤ coeffAbs n κ

  /-- Step 1: the shellwise local production is controlled by the finite sum of
      primitive modewise local production terms. -/
  hP_loc_le_sum_localProdCoeffXi :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
      1 ≤ k.val →
        supportData.split.P_loc n k
          ≤
        localProductionOfTerms modes (localProdTermOfCoeff Xi localProdCoeff) n k

#check @ActualModewiseLocalProductionCoeffData

theorem hlocalProd_le_pairTermXi_of_definition
    {K_max : ℕ}
    (ns : ActualModewiseLocalProductionCoeffData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      k.val < ns.supportData.Ncut →
      1 ≤ k.val →
      κ ∈ ns.modes →
        localProdTermOfCoeff ns.Xi ns.localProdCoeff n k κ
          ≤
        ns.localProdCoeff n k κ * ns.Xi n k := by
  intro n k κ hk hk1 hκ
  unfold localProdTermOfCoeff
  exact le_rfl

theorem hpairTerm_le_coeffAbs_of_localProdCoeff
    {K_max : ℕ}
    (ns : ActualModewiseLocalProductionCoeffData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ ns.modes →
        ns.localProdCoeff n k κ ≤ ns.coeffAbs n κ := by
  intro n k κ hκ
  exact ns.hlocalProdCoeff_le_coeffAbs n k κ hκ

#check @hlocalProd_le_pairTermXi_of_definition
#check @hpairTerm_le_coeffAbs_of_localProdCoeff

/-- The primitive modewise local production-coefficient data induce the previous
`ActualModewiseLocalPairingData`. -/
noncomputable def toActualModewiseLocalPairingData
    {K_max : ℕ}
    (ns : ActualModewiseLocalProductionCoeffData K_max) :
    ActualModewiseLocalPairingData K_max where
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
  modeWeightSq := ns.modeWeightSq
  hmodeWeightSq_nonneg := ns.hmodeWeightSq_nonneg
  hcoeffSq_le_modeWeightSq := ns.hcoeffSq_le_modeWeightSq
  shellEnergyTerm := shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff
  hshellEnergyTerm_nonneg :=
    shellEnergyTermOfModeEnergy_nonneg
      ns.shellFactor ns.modeEnergyCoeff
      ns.hshellFactor_nonneg ns.hmodeEnergyCoeff_nonneg
  hmodeWeightSq_le_shellEnergyTerm := ns.hmodeWeightSq_le_shellEnergyTerm
  hshellEnergySum_le_shellEnergy := hshellEnergySum_le_shellEnergy_of_modeEnergy
    (toActualModewiseShellBlockData {
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
      hpairing_Xi := by
        intro n k hk hk1
        exact le_trans
          (ns.hP_loc_le_sum_localProdCoeffXi n k hk hk1)
          (le_of_eq rfl)
      modes := ns.modes
      coeffAbs := ns.coeffAbs
      hcoeffAbs_nonneg := ns.hcoeffAbs_nonneg
      shellOf := ns.shellOf
      hshellOf_low := ns.hshellOf_low
      hcoeff_partition := ns.hcoeff_partition
      modeWeightSq := ns.modeWeightSq
      hmodeWeightSq_nonneg := ns.hmodeWeightSq_nonneg
      hcoeffSq_le_modeWeightSq := ns.hcoeffSq_le_modeWeightSq
      shellFactor := ns.shellFactor
      hshellFactor_nonneg := ns.hshellFactor_nonneg
      hshellFactor_le_on_block := ns.hshellFactor_le_on_block
      modeEnergyCoeff := ns.modeEnergyCoeff
      hmodeEnergyCoeff_nonneg := ns.hmodeEnergyCoeff_nonneg
      hmodeWeightSq_le_shellEnergyTerm := ns.hmodeWeightSq_le_shellEnergyTerm
      hmodeEnergyCoeff_sum_le_shellEnergy := ns.hmodeEnergyCoeff_sum_le_shellEnergy
    })
  pairTerm := ns.localProdCoeff
  hpairTerm_nonneg := ns.hlocalProdCoeff_nonneg
  hpairTerm_le_coeffAbs := hpairTerm_le_coeffAbs_of_localProdCoeff ns
  localProdTerm := localProdTermOfCoeff ns.Xi ns.localProdCoeff
  hP_loc_le_sum_localProd := ns.hP_loc_le_sum_localProdCoeffXi
  hlocalProd_le_pairTermXi := hlocalProd_le_pairTermXi_of_definition ns

#check @toActualModewiseLocalPairingData

/-- Therefore the primitive modewise local production-coefficient data already yield
the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_modewiseLocalProductionCoeff
    {K_max : ℕ}
    (ns : ActualModewiseLocalProductionCoeffData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_modewiseLocalPairing
      (toActualModewiseLocalPairingData ns)

#check @eventual_discrete_gronwall_of_modewiseLocalProductionCoeff

end NSLocalProductionTermActual
