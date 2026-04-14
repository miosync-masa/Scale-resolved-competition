import NSBarrier.NSFiniteBandBernsteinProof
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace NSLocalH1EnergyBound

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

-- ============================================================
-- SECTION 1: LOCAL H¹ ENERGY
-- ============================================================

/-- The low-shell H¹-type quantity:
    `localH1Energy = (∑_{k < Ncut} k² E_k)^{1/2}`. -/
noncomputable def localH1Energy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (Ncut : ℕ) (n : ℕ) : ℝ :=
  Real.sqrt ((lowShells (K_max := K_max) Ncut).sum
    (fun k : Fin K_max => ((k.val : ℝ) ^ 2) * Eshell n k))

#check @localH1Energy

theorem localH1Energy_nonneg {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (Ncut : ℕ) :
    ∀ n : ℕ, 0 ≤ localH1Energy Eshell Ncut n := by
  intro n
  unfold localH1Energy
  exact Real.sqrt_nonneg _

#check @localH1Energy_nonneg

/-- Weighted low-shell H¹ energy is bounded by `Ncut² * lowShellEnergy`. -/
theorem localH1Energy_sq_le_cutoff_sq_mul_lowShellEnergy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (Ncut : ℕ)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k) :
    ∀ n : ℕ,
      (lowShells (K_max := K_max) Ncut).sum
        (fun k : Fin K_max => ((k.val : ℝ) ^ 2) * Eshell n k)
        ≤
      ((Ncut : ℝ) ^ 2) * lowShellEnergy Eshell Ncut n := by
  intro n
  unfold lowShellEnergy lowShells
  calc
    ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < Ncut),
        ((k.val : ℝ) ^ 2) * Eshell n k
      ≤
    ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < Ncut),
        ((Ncut : ℝ) ^ 2) * Eshell n k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hklt : k.val < Ncut := (Finset.mem_filter.mp hk).2
          have hk_le : (k.val : ℝ) ≤ (Ncut : ℝ) := by
            exact_mod_cast Nat.le_of_lt hklt
          have hk_sq : ((k.val : ℝ) ^ 2) ≤ ((Ncut : ℝ) ^ 2) := by
            nlinarith
          exact mul_le_mul_of_nonneg_right hk_sq (hEn n k)
    _ = ((Ncut : ℝ) ^ 2) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < Ncut), Eshell n k := by
          symm
          rw [Finset.mul_sum]

#check @localH1Energy_sq_le_cutoff_sq_mul_lowShellEnergy

/-- Therefore `localH1Energy ≤ Ncut * sqrt(lowShellEnergy)`. -/
theorem localH1Energy_le_cutoff_sqrt_lowShellEnergy {K_max : ℕ}
    (Eshell : ShellEnergyTrajectory K_max) (Ncut : ℕ)
    (hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k) :
    ∀ n : ℕ,
      localH1Energy Eshell Ncut n
        ≤
      (Ncut : ℝ) * Real.sqrt (lowShellEnergy Eshell Ncut n) := by
  intro n
  have hsum_nonneg :
      0 ≤ (lowShells (K_max := K_max) Ncut).sum
        (fun k : Fin K_max => ((k.val : ℝ) ^ 2) * Eshell n k) := by
    refine Finset.sum_nonneg ?_
    intro k hk
    exact mul_nonneg (sq_nonneg (k.val : ℝ)) (hEn n k)
  have hlow_nonneg : 0 ≤ lowShellEnergy Eshell Ncut n :=
    lowShellEnergy_nonneg Eshell Ncut hEn n
  have hsq :
      (localH1Energy Eshell Ncut n)^2
        ≤
      (((Ncut : ℝ) * Real.sqrt (lowShellEnergy Eshell Ncut n)))^2 := by
    unfold localH1Energy
    rw [Real.sq_sqrt hsum_nonneg, mul_pow, Real.sq_sqrt hlow_nonneg]
    simpa [pow_two] using
      localH1Energy_sq_le_cutoff_sq_mul_lowShellEnergy Eshell Ncut hEn n
  have hnonneg_lhs : 0 ≤ localH1Energy Eshell Ncut n :=
    localH1Energy_nonneg Eshell Ncut n
  have hnonneg_rhs :
      0 ≤ (Ncut : ℝ) * Real.sqrt (lowShellEnergy Eshell Ncut n) := by
    positivity
  nlinarith

#check @localH1Energy_le_cutoff_sqrt_lowShellEnergy

-- ============================================================
-- SECTION 2: BRIDGE TO NSFiniteBandBernsteinProof
-- ============================================================

/-- Data where the local H¹ quantity is chosen canonically as
    `localH1Energy Eshell Ncut`.  The only remaining true analytic input
    is the Bernstein step `localStrainAmp ≤ A_bern * localH1Energy`. -/
structure ActualLocalH1EnergyBoundData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  C : ℝ
  ν : ℝ
  A_bern : ℝ

  hC : 0 ≤ C
  hν : 0 < ν
  hA_bern : 0 ≤ A_bern

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

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  /-- The finite-band Bernstein step, now with the canonical `localH1Energy`. -/
  hstrain_to_localH1Energy :
    ∀ n : ℕ,
      localStrainAmp n ≤ A_bern * localH1Energy Eshell supportData.Ncut n

#check @ActualLocalH1EnergyBoundData

/-- The canonical local-H¹ data induce the two-step Bernstein proof data,
    with `A_h1 = Ncut`. -/
noncomputable def toActualFiniteBandBernsteinProofData
    {K_max : ℕ}
    (ns : ActualLocalH1EnergyBoundData K_max) :
    ActualFiniteBandBernsteinProofData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  C := ns.C
  ν := ns.ν
  A_bern := ns.A_bern
  A_h1 := (ns.supportData.Ncut : ℝ)
  hC := ns.hC
  hν := ns.hν
  hA_bern := ns.hA_bern
  hA_h1 := by positivity
  hEn := ns.hEn
  hinc := ns.hinc
  htail := ns.htail
  hdecomp := ns.hdecomp
  hDiss := ns.hDiss
  hEtot := ns.hEtot
  localStrainAmp := ns.localStrainAmp
  hlocalStrain_nonneg := ns.hlocalStrain_nonneg
  localH1 := fun n => localH1Energy ns.Eshell ns.supportData.Ncut n
  hlocalH1_nonneg := localH1Energy_nonneg ns.Eshell ns.supportData.Ncut
  Xi := ns.Xi
  hXi_nonneg := ns.hXi_nonneg
  hD_def := ns.hD_def
  hpairing_Xi := ns.hpairing_Xi
  hP_loc_zero := ns.hP_loc_zero
  hstrain_to_H1 := ns.hstrain_to_localH1Energy
  hH1_to_energy := by
    intro n
    simpa using
      localH1Energy_le_cutoff_sqrt_lowShellEnergy
        ns.Eshell ns.supportData.Ncut ns.hEn n

#check @toActualFiniteBandBernsteinProofData

-- ============================================================
-- SECTION 3: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the canonical local-H¹ energy bound already yields
    the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_localH1EnergyBound
    {K_max : ℕ}
    (ns : ActualLocalH1EnergyBoundData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((ns.A_bern * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((ns.A_bern * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa using
    eventual_discrete_gronwall_of_finiteBandBernsteinProof
      (toActualFiniteBandBernsteinProofData ns)

#check @eventual_discrete_gronwall_of_localH1EnergyBound

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_localH1EnergyBound
    {K_max : ℕ}
    (ns : ActualLocalH1EnergyBoundData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((ns.A_bern * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_finiteBandBernsteinProof
      (toActualFiniteBandBernsteinProofData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_localH1EnergyBound

end NSLocalH1EnergyBound
