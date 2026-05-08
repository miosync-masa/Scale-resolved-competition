import NSBarrier.NSR3BernsteinProof
import NSBarrier.NSFiniteBandBernsteinActual
import Mathlib.Tactic

open scoped ENNReal

namespace NSR3FiniteBandSobolevBridge

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
open NSR3BernsteinProof
open NSR3ShellActual
open NSR3LittlewoodPaley
open MeasureTheory

/-- Actual `R³` finite-band closure data, where the Euclidean Bernstein constant
is obtained from a genuine finite-volume frequency support assumption. -/
structure ActualR3FiniteBandClosureData (K_max : ℕ) where
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

  localStrainAmp : ℕ → ℝ
  hlocalStrain_nonneg : ∀ n : ℕ, 0 ≤ localStrainAmp n

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
        supportData.split.P_loc n k ≤ localStrainAmp n * Xi n k
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  coeffAbs : ℕ → Frequency → ℝ
  hcoeff_nonneg : ∀ n : ℕ, ∀ ξ : Frequency, 0 ≤ coeffAbs n ξ
  hlocalStrain_l1 :
    ∀ n : ℕ, localStrainAmp n ≤ (eLpNorm (coeffAbs n) (1 : ℝ≥0∞) μR3).toReal
  hcoeff_mem2 :
    ∀ n : ℕ, MemLp (coeffAbs n) (2 : ℝ≥0∞) μR3
  hcoeff_support :
    ∀ n : ℕ,
      Function.support (coeffAbs n) ⊆ lowFrequencyCutoff supportData.Ncut
  hcoeff_l2_to_sqrtEnergy :
    ∀ n : ℕ,
      (eLpNorm (coeffAbs n) (2 : ℝ≥0∞) μR3).toReal
        ≤
      Real.sqrt (lowShellEnergy Eshell supportData.Ncut n)

/-- The Euclidean coefficient-side data induce the analytic Bernstein datum with
the low-shell energy square root as the target `L²` quantity. -/
noncomputable def toActualR3BernsteinData
    {K_max : ℕ}
    (ns : ActualR3FiniteBandClosureData K_max) :
    ActualR3BernsteinData where
  Ncut := ns.supportData.Ncut
  localStrainAmp := ns.localStrainAmp
  localH1Energy := fun n => Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n)
  coeffAbs := ns.coeffAbs
  hlocalStrain_nonneg := ns.hlocalStrain_nonneg
  hlocalH1_nonneg := by
    intro n
    exact Real.sqrt_nonneg _
  hcoeff_nonneg := ns.hcoeff_nonneg
  hlocalStrain_l1 := ns.hlocalStrain_l1
  hcoeff_mem2 := ns.hcoeff_mem2
  hcoeff_support := ns.hcoeff_support
  hcoeff_l2_to_localH1 := ns.hcoeff_l2_to_sqrtEnergy

/-- The Euclidean finite-band coefficient data yield the canonical square-root
closure bound needed by the existing barrier chain. -/
theorem r3_localStrain_sqrt
    {K_max : ℕ}
    (ns : ActualR3FiniteBandClosureData K_max) :
    ∀ n : ℕ,
      ns.localStrainAmp n
        ≤
      r3BernsteinConstant ns.supportData.Ncut
        * Real.sqrt (lowShellEnergy ns.Eshell ns.supportData.Ncut n) := by
  simpa using
    r3_localStrainAmp_le_bernsteinConstant_mul_localH1Energy
      (toActualR3BernsteinData ns)

/-- The Euclidean finite-band closure data induce the standard
`ActualFiniteBandBernsteinXiData` with theorem-backed constant
`r3BernsteinConstant Ncut`. -/
noncomputable def toActualFiniteBandBernsteinXiData
    {K_max : ℕ}
    (ns : ActualR3FiniteBandClosureData K_max) :
    ActualFiniteBandBernsteinXiData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  C := ns.C
  ν := ns.ν
  A := r3BernsteinConstant ns.supportData.Ncut
  hC := ns.hC
  hν := ns.hν
  hA := r3BernsteinConstant_nonneg ns.supportData.Ncut
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localStrainAmp := ns.localStrainAmp
  hlocalStrain_nonneg := ns.hlocalStrain_nonneg
  Xi := ns.Xi
  hXi_nonneg := ns.hXi_nonneg
  hD_def := ns.hD_def
  hpairing_Xi := ns.hpairing_Xi
  hP_loc_zero := ns.hP_loc_zero
  hlocalStrain_sqrt := r3_localStrain_sqrt ns

/-- Therefore the theorem-backed Euclidean finite-band Bernstein inequality
already yields the standard discrete Gronwall closure. -/
theorem r3_finite_band_closure_actual
    {K_max : ℕ}
    (ns : ActualR3FiniteBandClosureData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ r3BernsteinConstant ns.supportData.Ncut * Real.sqrt B / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + (r3BernsteinConstant ns.supportData.Ncut * Real.sqrt B / ns.ν) * ns.C) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_finiteBandBernsteinXi
      (toActualFiniteBandBernsteinXiData ns)

end NSR3FiniteBandSobolevBridge
