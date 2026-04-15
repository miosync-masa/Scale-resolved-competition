import NSBarrier.NSLocalH1EnergyBound
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open NSTorusShellActual

namespace NSFiniteFourierBernstein

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

/-- The Bernstein constant associated to a finite Fourier mode set. -/
noncomputable def bernsteinConstant (modes : Finset Mode) : ℝ :=
  Real.sqrt (modes.card : ℝ)

#check @bernsteinConstant

-- ============================================================
-- SECTION 1: ACTUAL FINITE FOURIER BERNSTEIN DATA
-- ============================================================

/-- Actual finite-Fourier Bernstein data.

Interpretation:
- `modes` is the finite set of active Fourier modes in the local finite band;
- `coeffAbs n κ` is the absolute size of the relevant Fourier coefficient
  contributing to the local strain amplitude at time `n`;
- `localStrainAmp n` is bounded by the ℓ¹ sum of those coefficient magnitudes;
- the ℓ² norm of those coefficients is controlled by the canonical `localH1Energy`.

Then Cauchy–Schwarz yields
  `localStrainAmp ≤ sqrt(card modes) * localH1Energy`.
-/
structure ActualFiniteFourierBernsteinData (K_max : ℕ) where
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

  /-- The local part of production vanishes on the zero shell. -/
  hP_loc_zero :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val = 0 → supportData.split.P_loc n k ≤ 0

  /-- The finite active Fourier mode set for the local strain amplitude. -/
  modes : Finset Mode

  /-- Absolute coefficient size on the active mode set. -/
  coeffAbs : ℕ → Mode → ℝ
  hcoeffAbs_nonneg : ∀ n : ℕ, ∀ κ : Mode, 0 ≤ coeffAbs n κ

  /-- ℓ¹ control of the local strain amplitude by the finite Fourier coefficients. -/
  hlocalStrain_l1 :
    ∀ n : ℕ,
      localStrainAmp n ≤ ∑ κ ∈ modes, coeffAbs n κ

  /-- ℓ² control of the same coefficients by the canonical local-H¹ energy. -/
  hcoeff_l2_to_localH1 :
    ∀ n : ℕ,
      ∑ κ ∈ modes, (coeffAbs n κ)^2
        ≤ (localH1Energy Eshell supportData.Ncut n)^2

#check @ActualFiniteFourierBernsteinData

-- ============================================================
-- SECTION 2: FINITE FOURIER BERNSTEIN INEQUALITY
-- ============================================================

/-- Cauchy–Schwarz on the finite active mode set gives the Bernstein bound
    `localStrainAmp ≤ sqrt(card modes) * localH1Energy`. -/
theorem localStrainAmp_le_bernsteinConstant_mul_localH1Energy
    {K_max : ℕ}
    (ns : ActualFiniteFourierBernsteinData K_max) :
    ∀ n : ℕ,
      ns.localStrainAmp n
        ≤
      bernsteinConstant ns.modes
        * localH1Energy ns.Eshell ns.supportData.Ncut n := by
  intro n
  let S : ℝ := ∑ κ ∈ ns.modes, ns.coeffAbs n κ
  let Q : ℝ := ∑ κ ∈ ns.modes, (ns.coeffAbs n κ)^2
  have hS_nonneg : 0 ≤ S := by
    unfold S
    exact Finset.sum_nonneg (by
      intro κ hκ
      exact ns.hcoeffAbs_nonneg n κ)
  have hH1_nonneg :
      0 ≤ localH1Energy ns.Eshell ns.supportData.Ncut n :=
    localH1Energy_nonneg ns.Eshell ns.supportData.Ncut n
  have hAmp_sq :
      (ns.localStrainAmp n)^2 ≤ S^2 := by
    have hAmp : ns.localStrainAmp n ≤ S := ns.hlocalStrain_l1 n
    nlinarith [ns.hlocalStrain_nonneg n, hS_nonneg]
  have hCS :
      S^2 ≤ (ns.modes.card : ℝ) * Q := by
    unfold S Q
    simpa [pow_two] using
      (sq_sum_le_card_mul_sum_sq
        (s := ns.modes)
        (f := fun κ : Mode => ns.coeffAbs n κ))
  have hQ :
      Q ≤ (localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
    unfold Q
    exact ns.hcoeff_l2_to_localH1 n
  have hcard_nonneg : 0 ≤ (ns.modes.card : ℝ) := by positivity
  have hSq :
      (ns.localStrainAmp n)^2
        ≤
      (bernsteinConstant ns.modes
        * localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
    have htmp :
        (ns.localStrainAmp n)^2
          ≤
        (ns.modes.card : ℝ)
          * (localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
      exact le_trans hAmp_sq (le_trans hCS (mul_le_mul_of_nonneg_left hQ hcard_nonneg))
    have hrewrite :
        (ns.modes.card : ℝ) * (localH1Energy ns.Eshell ns.supportData.Ncut n)^2
          =
        (bernsteinConstant ns.modes
          * localH1Energy ns.Eshell ns.supportData.Ncut n)^2 := by
      unfold bernsteinConstant
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact htmp.trans_eq hrewrite
  have hR_nonneg :
      0 ≤ bernsteinConstant ns.modes
            * localH1Energy ns.Eshell ns.supportData.Ncut n := by
    unfold bernsteinConstant
    positivity
  nlinarith [hSq, ns.hlocalStrain_nonneg n, hR_nonneg]

#check @localStrainAmp_le_bernsteinConstant_mul_localH1Energy

-- ============================================================
-- SECTION 3: BRIDGE TO NSLocalH1EnergyBound
-- ============================================================

/-- The finite Fourier Bernstein data induce the previous
    `ActualLocalH1EnergyBoundData`, with Bernstein constant
    `A_bern = sqrt(card modes)`. -/
noncomputable def toActualLocalH1EnergyBoundData
    {K_max : ℕ}
    (ns : ActualFiniteFourierBernsteinData K_max) :
    ActualLocalH1EnergyBoundData K_max where
  traj := ns.traj
  E := ns.E
  Eshell := ns.Eshell
  supportData := ns.supportData
  C := ns.C
  ν := ns.ν
  A_bern := bernsteinConstant ns.modes
  hC := ns.hC
  hν := ns.hν
  hA_bern := by
    unfold bernsteinConstant
    positivity
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
  hstrain_to_localH1Energy := localStrainAmp_le_bernsteinConstant_mul_localH1Energy ns

#check @toActualLocalH1EnergyBoundData

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the actual finite Fourier Bernstein estimate already yields
    the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_finiteFourierBernstein
    {K_max : ℕ}
    (ns : ActualFiniteFourierBernsteinData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt B) / ns.ν ∧
      ∀ m : ℕ,
        ns.E (N0 + m)
          ≤
        (1 + ((((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ))
                  * Real.sqrt B) / ns.ν) * ns.C)) ^ m
          * ns.E N0 := by
  simpa [bernsteinConstant] using
    eventual_discrete_gronwall_of_localH1EnergyBound
      (toActualLocalH1EnergyBoundData ns)

#check @eventual_discrete_gronwall_of_finiteFourierBernstein

/-- Uniform-ratio corollary. -/
theorem eventual_discrete_gronwall_of_uniform_finiteFourierBernstein
    {K_max : ℕ}
    (ns : ActualFiniteFourierBernsteinData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM :
      ∀ x : ℝ, 0 ≤ x →
        (((bernsteinConstant ns.modes * (ns.supportData.Ncut : ℝ)) * Real.sqrt x) / ns.ν) ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_localH1EnergyBound
      (toActualLocalH1EnergyBoundData ns) M hM hFM

#check @eventual_discrete_gronwall_of_uniform_finiteFourierBernstein

end NSFiniteFourierBernstein
