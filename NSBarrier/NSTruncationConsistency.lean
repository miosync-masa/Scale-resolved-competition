import NSBarrier.Basic
import NSBarrier.NSUniform
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open NSUniform

namespace NSTruncationConsistency

-- ============================================================
-- SECTION 1: SUCCESSOR TRUNCATION EMBEDDING
-- ============================================================

/-- Embed a shell index from truncation level `K` into the next truncation level `K+1`. -/
def succEmbed {K : ℕ} (k : Fin K) : Fin (K + 1) :=
  ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self K)⟩

@[simp] theorem succEmbed_val {K : ℕ} (k : Fin K) :
    (succEmbed k).val = k.val := rfl

#check @succEmbed
#check @succEmbed_val

-- ============================================================
-- SECTION 2: SHELL-DATA PRESERVATION
-- ============================================================

/-- One-step truncation consistency for shell data:
    each shell in truncation `K` is preserved when viewed inside truncation `K+1`. -/
def ShellDataPreservedStep (btraj : BudgetTrajectoryFamily) : Prop :=
  ∀ K n (k : Fin K),
    ((btraj K) n).P k = ((btraj (K + 1)) n).P (succEmbed k) ∧
    ((btraj K) n).D k = ((btraj (K + 1)) n).D (succEmbed k)

#check @ShellDataPreservedStep

/-- Stretching-dominance is preserved under successor truncation
    if shell data are preserved. -/
theorem isSD_preserved_step
    (btraj : BudgetTrajectoryFamily)
    (hpres : ShellDataPreservedStep btraj)
    (K n : ℕ)
    (k : Fin K) :
    isSD ((btraj K) n) k →
      isSD ((btraj (K + 1)) n) (succEmbed k) := by
  intro hk
  rcases hpres K n k with ⟨hP, hD⟩
  dsimp [isSD] at hk ⊢
  rwa [← hP, ← hD]

#check @isSD_preserved_step

-- ============================================================
-- SECTION 3: ACTIVE SHELLS AND THE FRONT
-- ============================================================

/-- Any stretching-dominated shell lies below the jump front. -/
theorem le_jumpFront_of_isSD
    {K_max : ℕ}
    (sb : ShellBudget K_max)
    {k : Fin K_max}
    (hk : isSD sb k) :
    k.val ≤ jumpFront sb := by
  classical
  have hmem : k ∈ activeShells sb := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ k, hk⟩
  have hne : (activeShells sb).Nonempty := ⟨k, hmem⟩
  have hleFin : k ≤ (activeShells sb).max' hne := by
    exact Finset.le_max' (activeShells sb) k hmem
  have hle : k.val ≤ ((activeShells sb).max' hne).val := by
    simpa using hleFin
  simpa [jumpFront, hne] using hle

#check @le_jumpFront_of_isSD

-- ============================================================
-- SECTION 4: CONSISTENT TRUNCATION
-- ============================================================

/-- If shell data are preserved under successor truncation,
    then the jump front is monotone in the truncation level. -/
theorem consistentTruncation_of_preserved_step
    (btraj : BudgetTrajectoryFamily)
    (hpres : ShellDataPreservedStep btraj) :
    ConsistentTruncation btraj := by
  intro K n
  classical
  by_cases hne : (activeShells ((btraj K) n)).Nonempty
  · let k : Fin K := (activeShells ((btraj K) n)).max' hne
    have hk_act : isSD ((btraj K) n) k := by
      exact (Finset.mem_filter.mp
        (Finset.max'_mem (activeShells ((btraj K) n)) hne)).2
    have hk_big : isSD ((btraj (K + 1)) n) (succEmbed k) :=
      isSD_preserved_step btraj hpres K n k hk_act
    have hsmall : jumpFront ((btraj K) n) = k.val := by
      simp [jumpFront, hne, k]
    have hbig : (succEmbed k).val ≤ jumpFront ((btraj (K + 1)) n) := by
      exact le_jumpFront_of_isSD ((btraj (K + 1)) n) hk_big
    calc
      jumpFront ((btraj K) n) = k.val := hsmall
      _ = (succEmbed k).val := by simp [succEmbed]
      _ ≤ jumpFront ((btraj (K + 1)) n) := hbig
  · have hsmall0 : jumpFront ((btraj K) n) = 0 := by
      simp [jumpFront, hne]
    rw [hsmall0]
    exact Nat.zero_le _

#check @consistentTruncation_of_preserved_step

end NSTruncationConsistency
