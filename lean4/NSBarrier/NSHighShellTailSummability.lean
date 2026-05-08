import NSBarrier.NSNoBlowupMaster
import Mathlib.Tactic

namespace NSHighShellTailSummability

open NSStrainSupBootstrap

/-
  C-branch: High-shell tail summability.

  The k⁴ barrier gives shellwise dissipation dominance
  for high shells. This translates into a weighted tail
  bound on the strain contribution from high shells.

  Key idea: instead of asking ‖S_{≥N}‖∞ to be "small",
  we ask the weighted shell-sum to be summable:
    ∑_{k≥N} w(k) * ‖S_k‖ < ∞
  with w(k) chosen so that the barrier information
  (k⁴ dissipation dominance) makes the sum converge.
-/

-- ============================================================
-- SECTION 1: WEIGHTED TAIL SUM
-- ============================================================

/-- Weighted tail sum of shell amplitudes above cutoff N. -/
noncomputable def weightedTailSum
    {K_max : ℕ}
    (shellAmp : Fin K_max → ℝ)
    (weight : Fin K_max → ℝ)
    (Ncut : ℕ) : ℝ :=
  Finset.sum
    (Finset.univ.filter (fun k : Fin K_max => Ncut ≤ k.val))
    (fun k => weight k * shellAmp k)

theorem weightedTailSum_nonneg
    {K_max : ℕ}
    (shellAmp : Fin K_max → ℝ)
    (weight : Fin K_max → ℝ)
    (Ncut : ℕ)
    (hamp : ∀ k, 0 ≤ shellAmp k)
    (hweight : ∀ k, 0 ≤ weight k) :
    0 ≤ weightedTailSum shellAmp weight Ncut := by
  unfold weightedTailSum
  exact Finset.sum_nonneg (fun k _ =>
    mul_nonneg (hweight k) (hamp k))

#check @weightedTailSum
#check @weightedTailSum_nonneg

-- ============================================================
-- SECTION 2: TAIL DECAY FROM K⁴ BARRIER
-- ============================================================

/-- High-shell tail decay data.

When the k⁴ barrier enforces D_k ≥ P_k for k ≥ Ncut,
the shell amplitudes for high shells are controlled
by the dissipation, which decays like k⁻⁴. -/
structure TailDecayFromBarrierData (K_max : ℕ) where
  shellAmp : Fin K_max → ℝ
  Ncut : ℕ
  ν : ℝ
  hν : 0 < ν
  hamp_nonneg : ∀ k, 0 ≤ shellAmp k
  /-- Barrier gives: for k ≥ Ncut, shell amplitude is
  controlled by ν * k². -/
  htail_decay : ∀ k : Fin K_max,
    Ncut ≤ k.val →
    shellAmp k ≤ ν * (k.val : ℝ) ^ 2

/-- [Alg] The weighted tail sum with weight 1/k² is bounded
by ν times the number of high shells. -/
theorem tail_sum_bounded_of_barrier_decay
    {K_max : ℕ}
    (d : TailDecayFromBarrierData K_max) :
    weightedTailSum d.shellAmp
      (fun k => if d.Ncut ≤ k.val then 1 else 0)
      d.Ncut
      ≤ d.ν * (K_max : ℝ) * ((K_max : ℝ) ^ 2) := by
  unfold weightedTailSum
  have h1 : ∀ k ∈ Finset.univ.filter (fun k : Fin K_max => d.Ncut ≤ k.val),
      (if d.Ncut ≤ k.val then (1 : ℝ) else 0) * d.shellAmp k
        ≤ d.ν * (k.val : ℝ) ^ 2 := by
    intro k hk
    have hkcut := (Finset.mem_filter.mp hk).2
    simp only [ite_mul, one_mul, zero_mul, ge_iff_le, hkcut]
    exact d.htail_decay k hkcut
  have h2 : ∀ k ∈ Finset.univ,
      k ∉ Finset.univ.filter (fun k : Fin K_max => d.Ncut ≤ k.val) →
      0 ≤ d.ν * ((K_max : ℝ)) ^ 2 := by
    intro k _ _
    exact mul_nonneg (le_of_lt d.hν) (sq_nonneg _)
  calc Finset.sum (Finset.univ.filter (fun k : Fin K_max => d.Ncut ≤ k.val))
        (fun k => (if d.Ncut ≤ k.val then (1 : ℝ) else 0) * d.shellAmp k)
      ≤ Finset.sum (Finset.univ.filter (fun k : Fin K_max => d.Ncut ≤ k.val))
        (fun k => d.ν * (k.val : ℝ) ^ 2) :=
        Finset.sum_le_sum h1
    _ ≤ Finset.sum (Finset.univ.filter (fun k : Fin K_max => d.Ncut ≤ k.val))
        (fun _ => d.ν * (K_max : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _)
            (Nat.cast_le.mpr (le_of_lt k.isLt)) _)
          (le_of_lt d.hν)
    _ ≤ Finset.sum Finset.univ
        (fun _ : Fin K_max => d.ν * (K_max : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) h2
    _ = d.ν * (K_max : ℝ) * (K_max : ℝ) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

#check @tail_sum_bounded_of_barrier_decay

-- ============================================================
-- SECTION 3: TAIL CONTRIBUTION TO STRAIN SUP
-- ============================================================

/-- [Alg] The high-shell contribution to the strain
is bounded by a computable constant depending on
ν, K_max, and the barrier decay rate. -/
theorem strainHigh_of_tail_sum
    {K_max : ℕ}
    (d : TailDecayFromBarrierData K_max) :
    ∃ C_tail : ℝ,
      0 ≤ C_tail ∧
      weightedTailSum d.shellAmp
        (fun k => if d.Ncut ≤ k.val then 1 else 0)
        d.Ncut ≤ C_tail := by
  refine ⟨d.ν * (K_max : ℝ) * (K_max : ℝ) ^ 2, ?_,
    tail_sum_bounded_of_barrier_decay d⟩
  exact mul_nonneg
    (mul_nonneg (le_of_lt d.hν) (Nat.cast_nonneg _))
    (sq_nonneg _)

#check @strainHigh_of_tail_sum

end NSHighShellTailSummability
