import NSBarrier.NSStrainOpVectorActual
import NSBarrier.NSVorticityTransportActualVec
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell (ShellProjectorData)
open NSTorusShellActual
open NSStrainOpVectorActual
open NSVorticityTransportActualVec
open NSFourier
open NSAnalyticA1Locality

namespace NSL2MultiplierTorusVec

-- ============================================================
-- SECTION 1: ACTUAL SCALAR × VECTOR L² MULTIPLIER ON T³
-- ============================================================

/-- Actual scalar-vector multiplier estimate on `T³`:
    ‖σ • ω‖_{L²} ≤ ‖σ‖_{L∞} ‖ω‖_{L²}. -/
theorem l2_scalar_smul_vec_eLpNorm_le
    (σ : T3 → ℂ)
    (ω : T3 → Vec3)
    (hω : AEStronglyMeasurable ω μT3) :
    MeasureTheory.eLpNorm (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3
      ≤
    MeasureTheory.eLpNorm σ ⊤ μT3
      * MeasureTheory.eLpNorm ω (2 : ℝ≥0∞) μT3 := by
  have h_smul :
      ∀ᵐ x ∂ μT3,
        ‖σ x • ω x‖₊ ≤
          (1 : NNReal) * ‖σ x‖₊ * ‖ω x‖₊ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [nnnorm_smul, mul_comm]
  simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using
    (MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm
      (p := (2 : ℝ≥0∞))
      (f := σ)
      (g := ω)
      (μ := μT3)
      hω
      (fun a b => a • b)
      (1 : NNReal)
      h_smul)

/-- The same scalar-vector multiplier estimate, but on actual `Lp` elements. -/
theorem l2_scalar_smul_vec_norm_le
    (σ : T3 → ℂ)
    (ω : T3 → Vec3)
    (hσ : MeasureTheory.MemLp σ ⊤ μT3)
    (hω : MeasureTheory.MemLp ω (2 : ℝ≥0∞) μT3)
    (hσω : MeasureTheory.MemLp (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3) :
    ‖MeasureTheory.MemLp.toLp (fun x => σ x • ω x) hσω‖
      ≤
    (MeasureTheory.eLpNorm σ ⊤ μT3).toReal
      * ‖MeasureTheory.MemLp.toLp ω hω‖ := by
  rw [MeasureTheory.Lp.norm_toLp (f := fun x => σ x • ω x) (hf := hσω),
      MeasureTheory.Lp.norm_toLp (f := ω) (hf := hω)]
  have hmain :
      MeasureTheory.eLpNorm (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3
        ≤
      MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm ω (2 : ℝ≥0∞) μT3 :=
    l2_scalar_smul_vec_eLpNorm_le σ ω hω.aestronglyMeasurable
  have hleft_ne :
      MeasureTheory.eLpNorm (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ne_of_lt hσω.eLpNorm_lt_top
  have hσ_ne : MeasureTheory.eLpNorm σ ⊤ μT3 ≠ ⊤ := by
    exact ne_of_lt hσ.eLpNorm_lt_top
  have hω_ne : MeasureTheory.eLpNorm ω (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ne_of_lt hω.eLpNorm_lt_top
  have hprod_ne :
      MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm ω (2 : ℝ≥0∞) μT3 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hσ_ne hω_ne
  have hmain' :
      (MeasureTheory.eLpNorm (fun x => σ x • ω x) (2 : ℝ≥0∞) μT3).toReal
        ≤
      (MeasureTheory.eLpNorm σ ⊤ μT3
        * MeasureTheory.eLpNorm ω (2 : ℝ≥0∞) μT3).toReal := by
    exact (ENNReal.toReal_le_toReal hleft_ne hprod_ne).2 hmain
  simpa [ENNReal.toReal_mul, hσ_ne, hω_ne] using hmain'

#check @l2_scalar_smul_vec_eLpNorm_le
#check @l2_scalar_smul_vec_norm_le

-- ============================================================
-- SECTION 2: POINTWISE DOMINATION -> ACTION_LE
-- ============================================================

/-- Pointwise domination in vector form gives an `L²` domination
    after passing to actual `Lp` elements. -/
theorem dominated_norm_of_pointwise_dom_vec
    {K_max : ℕ}
    (sad : ShellStrainOperatorVecData K_max)
    (hσω : ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => sad.sigma k x • sad.omega k x) (2 : ℝ≥0∞) μT3) :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp
          (fun x => (sad.Sop k x) (sad.omega k x))
          (sad.Z_mem k)‖
        ≤
      ‖MeasureTheory.MemLp.toLp
          (fun x => sad.sigma k x • sad.omega k x)
          (hσω k)‖ := by
  intro k
  rw [MeasureTheory.Lp.norm_toLp (f := fun x => (sad.Sop k x) (sad.omega k x)) (hf := sad.Z_mem k),
      MeasureTheory.Lp.norm_toLp (f := fun x => sad.sigma k x • sad.omega k x) (hf := hσω k)]
  exact ENNReal.toReal_mono
    (ne_of_lt (hσω k).eLpNorm_lt_top)
    (MeasureTheory.eLpNorm_mono_ae (pointwise_dom_of_operator_bound_vec sad k))

/-- The actual `L²` shellwise strain-action estimate derived from
    pointwise vector domination plus the actual scalar-vector multiplier bound. -/
theorem action_le_of_pointwise_dom_vec
    {K_max : ℕ}
    (sad : ShellStrainOperatorVecData K_max)
    (hσω : ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => sad.sigma k x • sad.omega k x) (2 : ℝ≥0∞) μT3) :
    ∀ k : Fin K_max,
      ‖MeasureTheory.MemLp.toLp
          (fun x => (sad.Sop k x) (sad.omega k x))
          (sad.Z_mem k)‖
        ≤
      sad.strainSup * ‖MeasureTheory.MemLp.toLp (sad.omega k) (sad.omega_mem k)‖ := by
  intro k
  have hdom :
      ‖MeasureTheory.MemLp.toLp
          (fun x => (sad.Sop k x) (sad.omega k x))
          (sad.Z_mem k)‖
        ≤
      ‖MeasureTheory.MemLp.toLp
          (fun x => sad.sigma k x • sad.omega k x)
          (hσω k)‖ :=
    dominated_norm_of_pointwise_dom_vec sad hσω k
  have hmult :
      ‖MeasureTheory.MemLp.toLp
          (fun x => sad.sigma k x • sad.omega k x)
          (hσω k)‖
        ≤
      (MeasureTheory.eLpNorm (sad.sigma k) ⊤ μT3).toReal
        * ‖MeasureTheory.MemLp.toLp (sad.omega k) (sad.omega_mem k)‖ :=
    l2_scalar_smul_vec_norm_le
      (sad.sigma k) (sad.omega k)
      (sad.sigma_mem k) (sad.omega_mem k) (hσω k)
  exact le_trans hdom <|
    le_trans hmult <|
      mul_le_mul_of_nonneg_right
        (sad.sigma_bound k)
        (norm_nonneg (MeasureTheory.MemLp.toLp (sad.omega k) (sad.omega_mem k)))

#check @dominated_norm_of_pointwise_dom_vec
#check @action_le_of_pointwise_dom_vec

-- ============================================================
-- SECTION 3: CORE PDE-FACING DATA WITHOUT action_le
-- ============================================================

/-- A PDE-facing shell transport package with `action_le` removed;
    it will be supplied by `action_le_of_pointwise_dom_vec`. -/
structure NavierStokesShellTransportVecCoreData (K_max : ℕ) where
  projData : ShellProjectorData L2VecT3 K_max

  vorticity : T3 → Vec3
  vorticity_mem : MeasureTheory.MemLp vorticity (2 : ℝ≥0∞) μT3

  shellOmega : Fin K_max → T3 → Vec3
  shellOmega_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (shellOmega k) (2 : ℝ≥0∞) μT3

  sigma : Fin K_max → T3 → ℂ
  sigma_mem : ∀ k : Fin K_max, MeasureTheory.MemLp (sigma k) ⊤ μT3
  sigmaOmega_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => sigma k x • shellOmega k x) (2 : ℝ≥0∞) μT3

  Sop : Fin K_max → T3 → Mat3
  stretch_mem :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp (fun x => (Sop k x) (shellOmega k x)) (2 : ℝ≥0∞) μT3

  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  sigma_bound :
    ∀ k : Fin K_max,
      (MeasureTheory.eLpNorm (sigma k) ⊤ μT3).toReal ≤ strainSup

  op_bound :
    ∀ k : Fin K_max, ∀ x : T3, ‖Sop k x‖ ≤ ‖sigma k x‖

  shellOmega_eq_proj :
    ∀ k : Fin K_max,
      MeasureTheory.MemLp.toLp (shellOmega k) (shellOmega_mem k)
        =
      projData.Pk k (MeasureTheory.MemLp.toLp vorticity vorticity_mem)

#check @NavierStokesShellTransportVecCoreData

/-- Forgetting `action_le`, the core data still determine the operator-valued
    shell strain data used by the vector A1 chain. -/
noncomputable def toShellStrainOperatorVecData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecCoreData K_max) :
    ShellStrainOperatorVecData K_max where
  sigma := ns.sigma
  omega := ns.shellOmega
  Sop := ns.Sop
  sigma_mem := ns.sigma_mem
  omega_mem := ns.shellOmega_mem
  Z_mem := ns.stretch_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  op_bound := ns.op_bound

#check @toShellStrainOperatorVecData

/-- The core PDE-facing data instantiate the full shell transport data,
    with `action_le` now derived rather than assumed. -/
noncomputable def toNavierStokesShellTransportVecData
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecCoreData K_max) :
    NavierStokesShellTransportVecData K_max where
  projData := ns.projData
  vorticity := ns.vorticity
  vorticity_mem := ns.vorticity_mem
  shellOmega := ns.shellOmega
  shellOmega_mem := ns.shellOmega_mem
  sigma := ns.sigma
  sigma_mem := ns.sigma_mem
  Sop := ns.Sop
  stretch_mem := ns.stretch_mem
  strainSup := ns.strainSup
  strainSup_nonneg := ns.strainSup_nonneg
  sigma_bound := ns.sigma_bound
  op_bound := ns.op_bound
  action_le := action_le_of_pointwise_dom_vec
    (toShellStrainOperatorVecData ns)
    ns.sigmaOmega_mem
  shellOmega_eq_proj := ns.shellOmega_eq_proj

#check @toNavierStokesShellTransportVecData

-- ============================================================
-- SECTION 4: FINAL BRIDGE TO ProductionFromStrainSup
-- ============================================================

/-- Therefore the core PDE-facing data already suffice to yield the abstract
    `ProductionFromStrainSup` required by the barrier pipeline. -/
theorem productionFromStrainSup_of_navierStokes_transport_core
    {K_max : ℕ}
    (ns : NavierStokesShellTransportVecCoreData K_max) :
    ProductionFromStrainSup
      (localizedProduction
        (localizedData (toNavierStokesShellTransportVecData ns)))
      (strainState (toNavierStokesShellTransportVecData ns)) := by
  exact
    productionFromStrainSup_of_navierStokes_transport
      (toNavierStokesShellTransportVecData ns)

#check @productionFromStrainSup_of_navierStokes_transport_core

end NSL2MultiplierTorusVec
