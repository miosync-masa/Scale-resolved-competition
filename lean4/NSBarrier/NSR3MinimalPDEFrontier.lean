import NSBarrier.NSR3NavierStokesFields
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory

namespace NSR3MinimalPDEFrontier

open NSR3ShellActual
open NSR3NavierStokesFields

noncomputable def sigmaFromOpNormR3 {K_max : ℕ}
    (Sop : Fin K_max → R3 → Mat3) :
    Fin K_max → R3 → ℂ :=
  fun k x => Complex.ofReal ‖Sop k x‖

@[simp] theorem norm_sigmaFromOpNormR3
    {K_max : ℕ}
    (Sop : Fin K_max → R3 → Mat3)
    (k : Fin K_max) (x : R3) :
    ‖sigmaFromOpNormR3 Sop k x‖ = ‖Sop k x‖ := by
  simp [sigmaFromOpNormR3]

theorem memLp_top_of_aestronglyMeasurable_and_ae_bound_R3
    {α : Type*} {E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {C : ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    MemLp f ⊤ μ := by
  refine ⟨hf_meas, ?_⟩
  simp only [eLpNorm_exponent_top]
  exact eLpNormEssSup_lt_top_of_ae_bound hf_bound

theorem sigmaFromOpNorm_aestronglyMeasurable_of_Sop_R3
    {K_max : ℕ}
    (Sop : Fin K_max → R3 → Mat3)
    (hSop_meas : ∀ k : Fin K_max, AEStronglyMeasurable (Sop k) μR3) :
    ∀ k : Fin K_max,
      AEStronglyMeasurable (sigmaFromOpNormR3 Sop k) μR3 := by
  intro k
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hSop_meas k).norm

theorem sigma_mem_of_aestronglyMeasurable_and_ae_bound_R3
    {K_max : ℕ}
    (Sop : Fin K_max → R3 → Mat3)
    (strainSup : ℝ)
    (hSop_meas : ∀ k : Fin K_max,
      AEStronglyMeasurable (sigmaFromOpNormR3 Sop k) μR3)
    (hSop_ae_bound : ∀ k : Fin K_max, ∀ᵐ x ∂ μR3, ‖Sop k x‖ ≤ strainSup) :
    ∀ k : Fin K_max,
    MemLp (sigmaFromOpNormR3 Sop k) ⊤ μR3 := by
  intro k
  exact memLp_top_of_aestronglyMeasurable_and_ae_bound_R3
    (hSop_meas k)
    (by
      filter_upwards [hSop_ae_bound k] with x hx
      simpa [norm_sigmaFromOpNormR3] using hx)

theorem sigmaOmega_memLp_of_sigma_mem_and_omega_mem_R3
    {σ : R3 → ℂ} {ω : R3 → Vec3}
    (hσ : MemLp σ ⊤ μR3)
    (hω : MemLp ω (2 : ℝ≥0∞) μR3) :
    MemLp (fun x => σ x • ω x) (2 : ℝ≥0∞) μR3 :=
  MemLp.smul (r := 2) hω hσ

theorem stretch_memLp_of_dominated_and_measurable_R3
    {stretch dominant : R3 → Vec3}
    (hstretch_meas : AEStronglyMeasurable stretch μR3)
    (hdominant_mem : MemLp dominant (2 : ℝ≥0∞) μR3)
    (hdom : ∀ᵐ x ∂μR3, ‖stretch x‖ ≤ ‖dominant x‖) :
    MemLp stretch (2 : ℝ≥0∞) μR3 := by
  exact hdominant_mem.of_le_mul hstretch_meas
    (hdom.mono fun x hx => by rwa [one_mul])

/-- Primitive Euclidean PDE-regularity data for the `R^3` branch. -/
structure PrimitiveR3StrainRegularityData (K_max : ℕ) where
  Sop : Fin K_max → R3 → Mat3
  vorticity : R3 → Vec3
  vorticity_mem : MemLp vorticity (2 : ℝ≥0∞) μR3
  shellOmega : Fin K_max → R3 → Vec3
  shellOmega_mem : ∀ k, MemLp (shellOmega k) (2 : ℝ≥0∞) μR3
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  Sop_meas : ∀ k, AEStronglyMeasurable (Sop k) μR3
  Sop_ae_bound : ∀ k, ∀ᵐ x ∂ μR3, ‖Sop k x‖ ≤ strainSup
  stretch : Fin K_max → R3 → Vec3
  stretch_mem : ∀ k, MemLp (stretch k) (2 : ℝ≥0∞) μR3
  stretch_eq :
    ∀ k, stretch k = fun x => (Sop k x) (shellOmega k x)
  stretch_dom_from_shell :
    ∀ k, ∀ᵐ x ∂ μR3,
      ‖(Sop k x) (shellOmega k x)‖ ≤ ‖sigmaFromOpNormR3 Sop k x • shellOmega k x‖

theorem true_fields_imply_minimal_pde_frontier_R3
    {K_max : ℕ}
    (d : PrimitiveR3StrainRegularityData K_max) :
    (∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 d.Sop k) ⊤ μR3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (d.Sop k x) (d.shellOmega k x)) (2 : ℝ≥0∞) μR3) := by
  constructor
  · exact
      sigma_mem_of_aestronglyMeasurable_and_ae_bound_R3
        d.Sop d.strainSup
        (sigmaFromOpNorm_aestronglyMeasurable_of_Sop_R3 d.Sop d.Sop_meas)
        d.Sop_ae_bound
  · intro k
    have hsigma_mem :
        MemLp (sigmaFromOpNormR3 d.Sop k) ⊤ μR3 :=
      sigma_mem_of_aestronglyMeasurable_and_ae_bound_R3
        d.Sop d.strainSup
        (sigmaFromOpNorm_aestronglyMeasurable_of_Sop_R3 d.Sop d.Sop_meas)
        d.Sop_ae_bound k
    have hsigmaOmega_mem :
        MemLp (fun x => sigmaFromOpNormR3 d.Sop k x • d.shellOmega k x) (2 : ℝ≥0∞) μR3 :=
      sigmaOmega_memLp_of_sigma_mem_and_omega_mem_R3 hsigma_mem (d.shellOmega_mem k)
    have hmeas : AEStronglyMeasurable (fun x => (d.Sop k x) (d.shellOmega k x)) μR3 := by
      have hstretch_meas : AEStronglyMeasurable (d.stretch k) μR3 :=
        (d.stretch_mem k).aestronglyMeasurable
      simpa [d.stretch_eq k] using hstretch_meas
    exact stretch_memLp_of_dominated_and_measurable_R3
      hmeas hsigmaOmega_mem (d.stretch_dom_from_shell k)

/-- C4 minimal-frontier theorem: Euclidean `R^3` true fields with measurable
strain operator, `L²` shell vorticity, and a.e. operator-norm control already
produce the `sigma ∈ L^\infty` and `stretch ∈ L^2` obligations needed
downstream. -/
theorem R3_minimal_pde_frontier
    {K_max : ℕ}
    (d : PrimitiveR3StrainRegularityData K_max) :
    (∀ k : Fin K_max, MemLp (sigmaFromOpNormR3 d.Sop k) ⊤ μR3) ∧
    (∀ k : Fin K_max,
      MemLp (fun x => (d.Sop k x) (d.shellOmega k x)) (2 : ℝ≥0∞) μR3) :=
  true_fields_imply_minimal_pde_frontier_R3 d

end NSR3MinimalPDEFrontier
