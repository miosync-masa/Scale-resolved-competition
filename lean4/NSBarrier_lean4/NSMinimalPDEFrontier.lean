import NSBarrier.NSStrainRegularityTheorems
import NSBarrier.NSActualSigmaBound
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShellActual
open NSStrainOpVectorActual
open NSActualSigmaBound

namespace NSMinimalPDEFrontier

/-
  Purpose: reduce sigma_mem and stretch_mem to their
  minimal PDE cores:
  - AEStronglyMeasurable + ae_bound -> MemLp top
  - MemLp top × MemLp 2 -> MemLp 2 (multiplier)
  - pointwise domination + measurability -> MemLp 2

  After this file, the genuine PDE frontier is:
  1. Sop_ae_bound (a.e. operator norm bound)
  2. Sop measurability
  3. omega measurability
  4. stretch measurability (or derived from Sop + omega)
-/

-- ============================================================
-- SECTION 1: C-BRANCH — sigma_mem from ae_bound + measurability
-- ============================================================

/-- [Alg] MemLp f top from AEStronglyMeasurable + a.e. bound.
This is the general Linfty membership theorem. -/
theorem memLp_top_of_aestronglyMeasurable_and_ae_bound
    {α : Type*} {E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {C : ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    MemLp f ⊤ μ := by
  refine ⟨hf_meas, ?_⟩
  simp only [eLpNorm_exponent_top]
  exact (eLpNormEssSup_lt_top_of_ae_bound hf_bound)

#check @memLp_top_of_aestronglyMeasurable_and_ae_bound

/-- [Alg] sigma_mem follows from measurability of Sop
and the a.e. operator norm bound. -/
theorem sigma_mem_of_aestronglyMeasurable_and_ae_bound
    {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3)
    (strainSup : ℝ)
    (hSop_meas : ∀ k : Fin K_max,
      AEStronglyMeasurable (sigmaFromOpNorm Sop k) μT3)
    (hSop_ae_bound : ∀ k : Fin K_max, ∀ᵐ x ∂μT3,
      ‖Sop k x‖ ≤ strainSup) :
    ∀ k : Fin K_max,
      MemLp (sigmaFromOpNorm Sop k) ⊤ μT3 := by
  intro k
  exact memLp_top_of_aestronglyMeasurable_and_ae_bound
    (hSop_meas k)
    (by filter_upwards [hSop_ae_bound k] with x hx; rwa [norm_sigmaFromOpNorm])

#check @sigma_mem_of_aestronglyMeasurable_and_ae_bound

-- ============================================================
-- SECTION 1.5: Sop_measurability FROM Sop MEASURABILITY
-- ============================================================

/-- [Alg] `sigmaFromOpNorm Sop k` is AEStronglyMeasurable
whenever `Sop k` itself is AEStronglyMeasurable.

This eliminates `Sop_measurability` as a separate assumption:
  AEStronglyMeasurable (Sop k)
    → AEStronglyMeasurable (fun x => ‖Sop k x‖)     [.norm]
    → AEStronglyMeasurable (fun x => ↑‖Sop k x‖)    [Complex.continuous_ofReal.comp_]
    = AEStronglyMeasurable (sigmaFromOpNorm Sop k)    [def] -/
theorem sigmaFromOpNorm_aestronglyMeasurable_of_Sop
    {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3)
    (hSop_meas : ∀ k : Fin K_max,
      AEStronglyMeasurable (Sop k) μT3) :
    ∀ k : Fin K_max,
      AEStronglyMeasurable (sigmaFromOpNorm Sop k) μT3 := by
  intro k
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hSop_meas k).norm

#check @sigmaFromOpNorm_aestronglyMeasurable_of_Sop

-- ============================================================
-- SECTION 2: D-BRANCH STEP 1 — sigmaOmega_mem from multiplier
-- ============================================================

/-- [Alg] MemLp (sigma • omega) 2 from sigma in Linfty
and omega in L2. This is the Linfty × L2 -> L2 multiplier. -/
theorem sigmaOmega_memLp_of_sigma_mem_and_omega_mem
    {σ : T3 → ℂ} {ω : T3 → Vec3}
    (hσ : MemLp σ ⊤ μT3)
    (hω : MemLp ω (2 : ℝ≥0∞) μT3) :
    MemLp (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3 :=
  MemLp.smul (r := 2) hω hσ

#check @sigmaOmega_memLp_of_sigma_mem_and_omega_mem

-- ============================================================
-- SECTION 3: D-BRANCH STEP 2 — stretch_mem from domination
-- ============================================================

/-- [Alg] MemLp stretch 2 from pointwise domination by a
function already in L2, plus measurability of stretch. -/
theorem stretch_memLp_of_dominated_and_measurable
    {stretch dominant : T3 → Vec3}
    (hstretch_meas : AEStronglyMeasurable stretch μT3)
    (hdominant_mem : MemLp dominant (2 : ℝ≥0∞) μT3)
    (hdom : ∀ᵐ x ∂μT3, ‖stretch x‖ ≤ ‖dominant x‖) :
    MemLp stretch (2 : ℝ≥0∞) μT3 := by
  exact hdominant_mem.of_le_mul hstretch_meas
    (hdom.mono fun x hx => by rwa [one_mul])

#check @stretch_memLp_of_dominated_and_measurable

-- ============================================================
-- SECTION 4: COMBINED — stretch_mem from first principles
-- ============================================================

/-- [Alg] stretch_mem from sigma_mem + omega_mem +
pointwise operator norm domination + stretch measurability.

This composes the full D-branch:
  sigma ∈ Linfty, omega ∈ L2
  -> sigma • omega ∈ L2
  -> ‖stretch(x)‖ ≤ ‖Sop(x)‖ * ‖omega(x)‖ ≤ ‖sigma(x) • omega(x)‖
  -> stretch ∈ L2
-/
theorem stretch_mem_of_first_principles
    {K_max : ℕ}
    (Sop : Fin K_max → T3 → Mat3)
    (omega : Fin K_max → T3 → Vec3)
    (strainSup : ℝ)
    (hSop_meas : ∀ k,
      AEStronglyMeasurable (sigmaFromOpNorm Sop k) μT3)
    (hSop_ae_bound : ∀ k, ∀ᵐ x ∂μT3,
      ‖Sop k x‖ ≤ strainSup)
    (homega_mem : ∀ k,
      MemLp (omega k) (2 : ℝ≥0∞) μT3)
    (hstretch_meas : ∀ k,
      AEStronglyMeasurable
        (fun x => (Sop k x) (omega k x)) μT3)
    (hstretch_dom : ∀ k, ∀ᵐ x ∂μT3,
      ‖(Sop k x) (omega k x)‖
        ≤ ‖sigmaFromOpNorm Sop k x • omega k x‖) :
    ∀ k,
      MemLp (fun x => (Sop k x) (omega k x))
        (2 : ℝ≥0∞) μT3 := by
  intro k
  have hsigma_mem :=
    sigma_mem_of_aestronglyMeasurable_and_ae_bound
      Sop strainSup hSop_meas hSop_ae_bound k
  have hsigmaOmega_mem :=
    sigmaOmega_memLp_of_sigma_mem_and_omega_mem
      hsigma_mem (homega_mem k)
  exact stretch_memLp_of_dominated_and_measurable
    (hstretch_meas k) hsigmaOmega_mem (hstretch_dom k)

#check @stretch_mem_of_first_principles

-- ============================================================
-- SECTION 5: MINIMAL PDE FRONTIER SUMMARY
-- ============================================================

/-!
## Minimal PDE Frontier

After `sigmaFromOpNorm_aestronglyMeasurable_of_Sop`,
the `Sop_measurability` assumption (on `sigmaFromOpNorm`)
is reduced to `AEStronglyMeasurable (Sop k)` (on Sop itself).

Combined with the bootstrap elimination of `Sop_ae_bound`
(see NSStrainSupBootstrap), the irreducible inputs are:

| Input | Type | Note |
|-------|------|------|
| `Sop_meas` | AEStronglyMeasurable (Sop k) | Sop itself measurable |
| `omega_mem` | MemLp (omega k) 2 | vorticity in L2 |

And these two are both consequences of `ω₀ ∈ L²`:
- `omega_mem` is the initial data assumption
- `Sop_meas` follows from ω₀ ∈ L² via Biot-Savart:
    ω ∈ L² → v ∈ H¹ → ∇v measurable → S = (∇v+∇vᵀ)/2 measurable

So the **absolute irreducible input is 1**:

    ω₀ ∈ L²(T³)    (initial vorticity has finite enstrophy)
-/

end NSMinimalPDEFrontier
