import NSBarrier.NSFiniteSourceConditionalGronwall
import Mathlib.Tactic

namespace NSGalerkinUniformEstimates

open NSFiniteSourceConditionalGronwall

/-- Uniform pointwise Gronwall data for a family of Galerkin truncations. -/
structure UniformGalerkinGronwallData (ι : Type*) where
  E : ι → ℕ → ℝ
  M : ℝ
  C : ℝ
  N0 : ℕ
  hM   : 0 ≤ M
  hMC  : 0 ≤ M * C
  hgronwall : ∀ (i : ι) (m : ℕ),
    (E i) (N0 + m) ≤ ((1 : ℝ) + M * C) ^ m * ((E i) N0)
  hinit : ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, (E i) N0 ≤ B0

#check @UniformGalerkinGronwallData

theorem uniform_enstrophy_bound_of_uniform_gronwall
    {ι : Type*} (d : UniformGalerkinGronwallData ι) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, ∀ m : ℕ,
      (d.E i) (d.N0 + m) ≤ (1 + d.M * d.C) ^ m * B0 := by
  rcases d.hinit with ⟨B0, hB0, hinit⟩
  refine ⟨B0, hB0, ?_⟩
  intro i m
  calc (d.E i) (d.N0 + m)
      ≤ (1 + d.M * d.C) ^ m * (d.E i) d.N0 := d.hgronwall i m
    _ ≤ (1 + d.M * d.C) ^ m * B0 := by
        exact mul_le_mul_of_nonneg_left (hinit i)
          (pow_nonneg (by linarith [d.hMC]) _)

#check @uniform_enstrophy_bound_of_uniform_gronwall

noncomputable def uniformGrowthFactor
    {ι : Type*} (d : UniformGalerkinGronwallData ι) (m : ℕ) : ℝ :=
  (1 + d.M * d.C) ^ m

theorem uniform_enstrophy_bound_with_growthFactor
    {ι : Type*} (d : UniformGalerkinGronwallData ι) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, ∀ m : ℕ,
      (d.E i) (d.N0 + m) ≤ uniformGrowthFactor d m * B0 := by
  simpa [uniformGrowthFactor] using
    uniform_enstrophy_bound_of_uniform_gronwall d

#check @uniformGrowthFactor
#check @uniform_enstrophy_bound_with_growthFactor

/-- Uniform low-shell dissipation data. -/
structure UniformGalerkinDissipationData (ι : Type*) where
  gronwallData : UniformGalerkinGronwallData ι
  Cdiss  : ℝ
  hCdiss : 0 ≤ Cdiss
  Dlow : ι → ℕ → ℝ
  hDlow : ∀ i : ι, ∀ m : ℕ,
    Dlow i (gronwallData.N0 + m)
      ≤ Cdiss * (gronwallData.E i) (gronwallData.N0 + m)

#check @UniformGalerkinDissipationData

theorem uniform_lowShell_dissipation_bound
    {ι : Type*} (d : UniformGalerkinDissipationData ι) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, ∀ m : ℕ,
      d.Dlow i (d.gronwallData.N0 + m)
        ≤ d.Cdiss * (1 + d.gronwallData.M * d.gronwallData.C) ^ m * B0 := by
  rcases uniform_enstrophy_bound_of_uniform_gronwall
    d.gronwallData with ⟨B0, hB0, hE⟩
  refine ⟨B0, hB0, ?_⟩
  intro i m
  calc d.Dlow i (d.gronwallData.N0 + m)
      ≤ d.Cdiss * (d.gronwallData.E i) (d.gronwallData.N0 + m) :=
        d.hDlow i m
    _ ≤ d.Cdiss * ((1 + d.gronwallData.M * d.gronwallData.C) ^ m * B0) :=
        mul_le_mul_of_nonneg_left (hE i m) d.hCdiss
    _ = d.Cdiss * (1 + d.gronwallData.M * d.gronwallData.C) ^ m * B0 := by
        ring

#check @uniform_lowShell_dissipation_bound

theorem galerkin_uniform_enstrophy_master
    {ι : Type*} (d : UniformGalerkinGronwallData ι) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, ∀ m : ℕ,
      (d.E i) (d.N0 + m) ≤ (1 + d.M * d.C) ^ m * B0 :=
  uniform_enstrophy_bound_of_uniform_gronwall d

theorem galerkin_uniform_dissipation_master
    {ι : Type*} (d : UniformGalerkinDissipationData ι) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ i : ι, ∀ m : ℕ,
      d.Dlow i (d.gronwallData.N0 + m)
        ≤ d.Cdiss * (1 + d.gronwallData.M * d.gronwallData.C) ^ m * B0 :=
  uniform_lowShell_dissipation_bound d

#check @galerkin_uniform_enstrophy_master
#check @galerkin_uniform_dissipation_master

end NSGalerkinUniformEstimates
