import NSBarrier.NSFourier
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

open NSFourier
open scoped InnerProductSpace

/-!
# Pairing Bound for Shell-Resolved Enstrophy Production

The core Fourier-analytic input for the barrier framework:
  P_k = inner(omega_k, S omega_k) <= norm_S_op * norm_omega_k^2

Proved via Cauchy-Schwarz + operator norm.

## Authors
Masamichi Iizumi, Tamaki Iizumi, Miosync Inc.
-/

namespace NSPairingBound

-- SECTION 1: ABSTRACT PAIRING BOUND

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- Core pairing bound (Cauchy-Schwarz + operator norm):
    inner(v, A v) <= norm(A) * norm(v)^2. -/
theorem inner_apply_le_opNorm_mul_sq
    (A : V →L[ℝ] V) (v : V) :
    ⟪v, A v⟫_ℝ ≤ ‖A‖ * ‖v‖ ^ 2 := by
  calc ⟪v, A v⟫_ℝ
      ≤ ‖v‖ * ‖A v‖ := real_inner_le_norm v (A v)
    _ ≤ ‖v‖ * (‖A‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg v)
    _ = ‖A‖ * ‖v‖ ^ 2 := by ring

omit [CompleteSpace V] in
/-- Variant with explicit bound: if norm(A) <= C then inner(v, A v) <= C * norm(v)^2. -/
theorem inner_apply_le_of_opNorm_le
    (A : V →L[ℝ] V) (v : V) (C : ℝ)
    (hC : ‖A‖ ≤ C) :
    ⟪v, A v⟫_ℝ ≤ C * ‖v‖ ^ 2 := by
  have h1 := inner_apply_le_opNorm_mul_sq A v
  have h2 : ‖A‖ * ‖v‖ ^ 2 ≤ C * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  linarith

#check @inner_apply_le_opNorm_mul_sq
#check @inner_apply_le_of_opNorm_le

-- SECTION 2: SHELL-RESOLVED PRODUCTION BOUND

/-- Shell-resolved pairing data on a single Hilbert space V.
    V = L^2(T^3)^3 in the physical setting. -/
structure ShellPairingData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K_max : ℕ) where
  omega : Fin K_max → V
  S : V →L[ℝ] V
  strainSup : ℝ
  strainSup_nonneg : 0 ≤ strainSup
  S_le : ‖S‖ ≤ strainSup

noncomputable def shellProduction {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) (k : Fin K_max) : ℝ :=
  ⟪spd.omega k, spd.S (spd.omega k)⟫_ℝ

noncomputable def shellVortSq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) (k : Fin K_max) : ℝ :=
  ‖spd.omega k‖ ^ 2

/-- Shell pairing bound: P_k <= strainSup * norm(omega_k)^2. -/
theorem shell_pairing_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) :
    ∀ k : Fin K_max,
      shellProduction spd k ≤ spd.strainSup * shellVortSq spd k := by
  intro k
  exact inner_apply_le_of_opNorm_le spd.S (spd.omega k) spd.strainSup spd.S_le

theorem shellVortSq_nonneg {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) :
    ∀ k, 0 ≤ shellVortSq spd k := by
  intro k; unfold shellVortSq; positivity

#check @shell_pairing_bound
#check @shellVortSq_nonneg

-- SECTION 3: BRIDGE TO ProductionFromStrainSup

noncomputable def toFourierState {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) : FourierState K_max where
  shellEnergy := shellVortSq spd
  shellVorticitySq := shellVortSq spd
  strainSup := spd.strainSup

/-- Bridge: pairing bound yields ProductionFromStrainSup. -/
theorem productionFromStrainSup_of_pairing
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {K_max : ℕ}
    (spd : ShellPairingData V K_max) :
    ProductionFromStrainSup
      (shellProduction spd)
      (toFourierState spd) := by
  intro k
  simp only [toFourierState]
  exact shell_pairing_bound spd k

theorem toFourierState_shellEnergyNonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ} (spd : ShellPairingData V K_max) :
    ShellEnergyNonneg (toFourierState spd) :=
  shellVortSq_nonneg spd

theorem toFourierState_shellVorticitySqNonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K_max : ℕ} (spd : ShellPairingData V K_max) :
    ShellVorticitySqNonneg (toFourierState spd) :=
  shellVortSq_nonneg spd

#check @toFourierState
#check @productionFromStrainSup_of_pairing
#check @toFourierState_shellEnergyNonneg

end NSPairingBound
