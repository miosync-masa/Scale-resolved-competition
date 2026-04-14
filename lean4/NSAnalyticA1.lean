import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformA1Bridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSBridge
open NSUniform
open NSUniformA1Bridge

namespace NSAnalyticA1

-- ============================================================
-- SECTION 1: SHELLWISE L2 AND PROJECTED-STRETCH NORMS
-- ============================================================

/-- A shellwise L2-size for vorticity, intended to model `‖ω_k‖_2`. -/
def ShellVorticityL2 (K_max : ℕ) := FourierState K_max → Fin K_max → ℝ

/-- A shellwise projected-stretch norm, intended to model
    `‖P_k[(ω · ∇)v]‖_2`. -/
def ProjectedStretchL2 (K_max : ℕ) :=
  ShellBudget K_max → FourierState K_max → Fin K_max → ℝ

/-- A family of shellwise vorticity L2-profiles indexed by truncation level. -/
def ShellVorticityL2Family := ∀ K_max : ℕ, ShellVorticityL2 K_max

/-- A family of shellwise projected-stretch profiles indexed by truncation level. -/
def ProjectedStretchL2Family := ∀ K_max : ℕ, ProjectedStretchL2 K_max

#check @ShellVorticityL2
#check @ProjectedStretchL2
#check @ShellVorticityL2Family
#check @ProjectedStretchL2Family

-- ============================================================
-- SECTION 2: POINTWISE A1 HYPOTHESES
-- ============================================================

/-- Pointwise nonnegativity of the shellwise vorticity L2-size. -/
def ShellVorticityL2NonnegAt {K_max : ℕ}
    (fs : FourierState K_max)
    (ωL2 : ShellVorticityL2 K_max) : Prop :=
  ∀ k : Fin K_max, 0 ≤ ωL2 fs k

/-- Pointwise identification of `shellVorticitySq` with the square of a shellwise
    vorticity L2-size. -/
def ShellVorticityL2SqMatchesAt {K_max : ℕ}
    (fs : FourierState K_max)
    (ωL2 : ShellVorticityL2 K_max) : Prop :=
  ∀ k : Fin K_max, (ωL2 fs k) ^ 2 = fs.shellVorticitySq k

/-- Pairing estimate for shellwise production:
    `P_k ≤ ‖ω_k‖_2 · ‖P_k[(ω·∇)v]‖_2`. -/
def ShellProductionPairingBound {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (ωL2 : ShellVorticityL2 K_max)
    (projL2 : ProjectedStretchL2 K_max) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ ωL2 fs k * projL2 sb fs k

/-- Localized projected-stretch estimate:
    `‖P_k[(ω·∇)v]‖_2 ≤ G · ‖ω_k‖_2`. -/
def LocalizedProjectedStretchEstimate {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (ωL2 : ShellVorticityL2 K_max)
    (projL2 : ProjectedStretchL2 K_max) : Prop :=
  ∀ k : Fin K_max, projL2 sb fs k ≤ G fs * ωL2 fs k

#check @ShellVorticityL2NonnegAt
#check @ShellVorticityL2SqMatchesAt
#check @ShellProductionPairingBound
#check @LocalizedProjectedStretchEstimate

-- ============================================================
-- SECTION 3: POINTWISE A1 THEOREMS
-- ============================================================

/-- From the pairing bound and the localized projected-stretch estimate,
    one obtains the shellwise localized production bound
    `P_k ≤ G · Ξ_k`. -/
theorem localizedProduction_from_pairing_and_projection {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (ωL2 : ShellVorticityL2 K_max)
    (projL2 : ProjectedStretchL2 K_max)
    (hω_nonneg : ShellVorticityL2NonnegAt fs ωL2)
    (hω_sq : ShellVorticityL2SqMatchesAt fs ωL2)
    (hpair : ShellProductionPairingBound sb fs ωL2 projL2)
    (hproj : LocalizedProjectedStretchEstimate sb fs G ωL2 projL2) :
    LocalizedProductionFromGradient sb fs G := by
  intro k
  have h1 : sb.P k ≤ ωL2 fs k * projL2 sb fs k := hpair k
  have h2 : projL2 sb fs k ≤ G fs * ωL2 fs k := hproj k
  have hωk : 0 ≤ ωL2 fs k := hω_nonneg k
  have hmul :
      ωL2 fs k * projL2 sb fs k ≤
        ωL2 fs k * (G fs * ωL2 fs k) := by
    exact mul_le_mul_of_nonneg_left h2 hωk
  calc
    sb.P k ≤ ωL2 fs k * projL2 sb fs k := h1
    _ ≤ ωL2 fs k * (G fs * ωL2 fs k) := hmul
    _ = G fs * (ωL2 fs k) ^ 2 := by ring
    _ = G fs * fs.shellVorticitySq k := by rw [hω_sq k]

/-- Combining the previous theorem with gradient-to-strain control gives the
    shellwise `ProductionFromStrainSup` hypothesis required by the Fourier layer,
    after scaling the strain amplitude by `C_str`. -/
theorem productionFromStrainSup_from_pairing_and_projection {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str : ℝ)
    (ωL2 : ShellVorticityL2 K_max)
    (projL2 : ProjectedStretchL2 K_max)
    (hXi_nonneg : ShellVorticitySqNonneg fs)
    (hω_nonneg : ShellVorticityL2NonnegAt fs ωL2)
    (hω_sq : ShellVorticityL2SqMatchesAt fs ωL2)
    (hpair : ShellProductionPairingBound sb fs ωL2 projL2)
    (hproj : LocalizedProjectedStretchEstimate sb fs G ωL2 projL2)
    (hgc : GradientControlledByStrain fs G C_str) :
    ProductionFromStrainSup sb.P
      { fs with strainSup := C_str * fs.strainSup } := by
  have hloc : LocalizedProductionFromGradient sb fs G :=
    localizedProduction_from_pairing_and_projection
      sb fs G ωL2 projL2 hω_nonneg hω_sq hpair hproj
  exact physical_production_from_strain_sup_step sb fs G C_str hXi_nonneg hloc hgc

#check @localizedProduction_from_pairing_and_projection
#check @productionFromStrainSup_from_pairing_and_projection

-- ============================================================
-- SECTION 4: UNIFORM A1 HYPOTHESES
-- ============================================================

/-- Uniform pointwise nonnegativity of the shellwise vorticity L2-size. -/
def UniformShellVorticityL2Nonneg
    (ftraj : FourierTrajectoryFamily)
    (ωL2fam : ShellVorticityL2Family) : Prop :=
  ∀ K_max n, ShellVorticityL2NonnegAt (ftraj K_max (n + 1)) (ωL2fam K_max)

/-- Uniform pointwise identification of `shellVorticitySq` with the square of
    a shellwise vorticity L2-size. -/
def UniformShellVorticityL2SqMatches
    (ftraj : FourierTrajectoryFamily)
    (ωL2fam : ShellVorticityL2Family) : Prop :=
  ∀ K_max n, ShellVorticityL2SqMatchesAt (ftraj K_max (n + 1)) (ωL2fam K_max)

/-- Eventually, shellwise production satisfies the pairing estimate,
    uniformly in `K_max`. -/
def UniformShellProductionPairingBound
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ωL2fam : ShellVorticityL2Family)
    (projFam : ProjectedStretchL2Family) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    ShellProductionPairingBound
      ((btraj K_max) (n + 1))
      (ftraj K_max (n + 1))
      (ωL2fam K_max)
      (projFam K_max)

/-- Eventually, the localized projected-stretch estimate holds,
    uniformly in `K_max`. -/
def UniformLocalizedProjectedStretchEstimate
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ωL2fam : ShellVorticityL2Family)
    (projFam : ProjectedStretchL2Family) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    LocalizedProjectedStretchEstimate
      ((btraj K_max) (n + 1))
      (ftraj K_max (n + 1))
      (Gfam K_max)
      (ωL2fam K_max)
      (projFam K_max)

#check @UniformShellVorticityL2Nonneg
#check @UniformShellVorticityL2SqMatches
#check @UniformShellProductionPairingBound
#check @UniformLocalizedProjectedStretchEstimate

-- ============================================================
-- SECTION 5: UNIFORM A1 THEOREMS
-- ============================================================

/-- Uniform pairing and localized projected-stretch estimates imply the uniform
    shellwise localized production bound `P_k ≤ G · Ξ_k`. -/
theorem uniform_localizedProduction_from_pairing_and_projection
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (ωL2fam : ShellVorticityL2Family)
    (projFam : ProjectedStretchL2Family)
    (hω_nonneg : UniformShellVorticityL2Nonneg ftraj ωL2fam)
    (hω_sq : UniformShellVorticityL2SqMatches ftraj ωL2fam)
    (hpair : UniformShellProductionPairingBound btraj ftraj ωL2fam projFam)
    (hproj : UniformLocalizedProjectedStretchEstimate btraj ftraj Gfam ωL2fam projFam) :
    UniformLocalizedProductionFromGradient btraj ftraj Gfam := by
  rcases hpair with ⟨Np, hpair'⟩
  rcases hproj with ⟨Nq, hproj'⟩
  refine ⟨max Np Nq, ?_⟩
  intro K_max n hn
  have hNp : Np ≤ n := by
    exact le_trans (le_max_left Np Nq) hn
  have hNq : Nq ≤ n := by
    exact le_trans (le_max_right Np Nq) hn
  exact
    localizedProduction_from_pairing_and_projection
      ((btraj K_max) (n + 1))
      (ftraj K_max (n + 1))
      (Gfam K_max)
      (ωL2fam K_max)
      (projFam K_max)
      (hω_nonneg K_max n)
      (hω_sq K_max n)
      (hpair' K_max n hNp)
      (hproj' K_max n hNq)

/-- Uniform pairing and localized projected-stretch estimates, together with
    gradient-to-strain control, imply the uniform shellwise
    `ProductionFromStrainSup` hypothesis after scaling the strain trajectory. -/
theorem uniform_productionFromStrainSup_from_pairing_and_projection
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (C_str : ℝ)
    (ωL2fam : ShellVorticityL2Family)
    (projFam : ProjectedStretchL2Family)
    (hXi_nonneg : UniformShellVorticitySqNonneg ftraj)
    (hω_nonneg : UniformShellVorticityL2Nonneg ftraj ωL2fam)
    (hω_sq : UniformShellVorticityL2SqMatches ftraj ωL2fam)
    (hpair : UniformShellProductionPairingBound btraj ftraj ωL2fam projFam)
    (hproj : UniformLocalizedProjectedStretchEstimate btraj ftraj Gfam ωL2fam projFam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str) :
    UniformProductionFromStrainSup btraj (scaledStrainTrajectory ftraj C_str) := by
  have hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam :=
    uniform_localizedProduction_from_pairing_and_projection
      btraj ftraj Gfam ωL2fam projFam hω_nonneg hω_sq hpair hproj
  exact
    uniform_productionFromStrainSup_from_locality
      btraj ftraj Gfam C_str hXi_nonneg hloc hgc

#check @uniform_localizedProduction_from_pairing_and_projection
#check @uniform_productionFromStrainSup_from_pairing_and_projection

end NSAnalyticA1
