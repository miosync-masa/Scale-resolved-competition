import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# NS Barrier: k⁴ Dissipative Barrier for Navier-Stokes

## Authors
Masamichi Iizumi, Tamaki Iizumi
Miosync, Inc., Tokyo, Japan
-/

-- SECTION 1: DEFINITIONS

structure ShellBudget (K_max : ℕ) where
  P : Fin K_max → ℝ
  D : Fin K_max → ℝ
  D_nonneg : ∀ k, 0 ≤ D k

def isSD {K_max : ℕ} (sb : ShellBudget K_max) (k : Fin K_max) : Prop :=
  sb.D k < sb.P k

/-- Active shells: the set of stretching-dominated shells. -/
noncomputable def activeShells {K_max : ℕ} (sb : ShellBudget K_max) :
    Finset (Fin K_max) :=
  Finset.univ.filter (fun k : Fin K_max => sb.D k < sb.P k)

/-- The jump front (max'-based, no let binding). -/
noncomputable def jumpFront {K_max : ℕ} (sb : ShellBudget K_max) : ℕ :=
  if hS : (activeShells sb).Nonempty then
    ((activeShells sb).max' hS).val
  else
    0

def corridorStep {K_max : ℕ} (sb₁ sb₂ : ShellBudget K_max) : Prop :=
  jumpFront sb₁ < jumpFront sb₂

noncomputable def frontCost {K_max : ℕ} (sb : ShellBudget K_max) (S : Finset ℕ) : ℝ :=
  S.sum (fun k => if h : k < K_max then sb.D ⟨k, h⟩ else 0)

def k4Cost (ν : ℝ) (k : ℕ) : ℝ := ν * (k : ℝ) ^ 4

noncomputable def barrierFn {K_max : ℕ} (sb : ShellBudget K_max) (Φ ν : ℝ) : ℝ :=
  Φ - k4Cost ν (jumpFront sb)

-- SECTION 2: STRUCTURAL LEMMAS

theorem corridorStep_implies_lt {K_max : ℕ} (B₁ B₂ : ShellBudget K_max) :
    corridorStep B₁ B₂ → jumpFront B₁ < jumpFront B₂ := by
  intro h; exact h

theorem frontCost_nonneg {K_max : ℕ} (B : ShellBudget K_max) (S : Finset ℕ) :
    0 ≤ frontCost B S := by
  unfold frontCost
  apply Finset.sum_nonneg
  intro k _
  split
  · exact B.D_nonneg _
  · exact le_refl 0

theorem k4Cost_nonneg {ν : ℝ} (hν : 0 ≤ ν) (k : ℕ) : 0 ≤ k4Cost ν k := by
  unfold k4Cost; apply mul_nonneg hν; positivity

theorem k4Cost_mono {ν : ℝ} (hν : 0 ≤ ν) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    k4Cost ν k₁ ≤ k4Cost ν k₂ := by
  unfold k4Cost
  apply mul_le_mul_of_nonneg_left _ hν
  exact pow_le_pow_left₀ (Nat.cast_nonneg k₁) (Nat.cast_le.mpr hk) 4

-- SECTION 3: k⁴ BARRIER

theorem nat_pow4_unbounded (A : ℕ) : ∃ N : ℕ, A < N ^ 4 := by
  use A + 1
  have h1 : 1 ≤ A + 1 := Nat.succ_le_succ (Nat.zero_le A)
  calc A < A + 1 := Nat.lt_succ_iff.mpr le_rfl
    _ = (A + 1) ^ 1 := (pow_one _).symm
    _ ≤ (A + 1) ^ 4 := Nat.pow_le_pow_right h1 (by norm_num : 1 ≤ 4)

theorem k4Cost_unbounded {ν : ℝ} (hν : 0 < ν) (A : ℝ) :
    ∃ N : ℕ, A < k4Cost ν N := by
  obtain ⟨M, hM⟩ := exists_nat_gt (A / ν)
  obtain ⟨N, hN⟩ := nat_pow4_unbounded M
  use N
  unfold k4Cost
  rw [show (N : ℝ) ^ 4 = ((N ^ 4 : ℕ) : ℝ) from by push_cast; ring]
  calc A = ν * (A / ν) := by field_simp
    _ < ν * (M : ℝ) := by apply mul_lt_mul_of_pos_left hM hν
    _ < ν * ((N ^ 4 : ℕ) : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hν
        exact Nat.cast_lt.mpr hN

theorem barrier_eventually_negative (Φ ν : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → Φ - k4Cost ν k < 0 := by
  obtain ⟨N, hN⟩ := k4Cost_unbounded hν Φ
  exact ⟨N, fun k hk => by linarith [k4Cost_mono (le_of_lt hν) hk]⟩

-- SECTION 4: FRONT WITNESS AND CONNECTION

/-- If jumpFront > 0, the front value is realized by an actual shell. -/
theorem jumpFront_realized_of_pos {K_max : ℕ} (sb : ShellBudget K_max) :
    0 < jumpFront sb →
    ∃ k : Fin K_max, sb.D k < sb.P k ∧ k.val = jumpFront sb := by
  classical
  intro hpos
  by_cases hS : (activeShells sb).Nonempty
  · refine ⟨(activeShells sb).max' hS, ?_, ?_⟩
    · have hmem : (activeShells sb).max' hS ∈ activeShells sb :=
        Finset.max'_mem (activeShells sb) hS
      exact (Finset.mem_filter.mp hmem).2
    · simp [jumpFront, hS]
  · exfalso
    simp [jumpFront, dif_neg hS] at hpos

theorem barrierFn_neg_of_large_front {K_max : ℕ} (sb : ShellBudget K_max)
    (Φ ν : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, N ≤ jumpFront sb → barrierFn sb Φ ν < 0 := by
  obtain ⟨N, hN⟩ := barrier_eventually_negative Φ ν hν
  exact ⟨N, fun h => by unfold barrierFn; exact hN (jumpFront sb) h⟩

theorem no_advance_past_barrier {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max) (Φ ν : ℝ)
    (hbarrier : barrierFn sb₂ Φ ν < 0)
    (hcost : ∀ k : Fin K_max, sb₂.D k < sb₂.P k →
      Φ ≤ k4Cost ν k.val → False) :
    ¬ corridorStep sb₁ sb₂ := by
  intro hstep
  have hpos : 0 < jumpFront sb₂ := lt_of_le_of_lt (Nat.zero_le _) hstep
  obtain ⟨k, hsd, hk⟩ := jumpFront_realized_of_pos sb₂ hpos
  have hPhi : Φ ≤ k4Cost ν k.val := by
    have : Φ < k4Cost ν (jumpFront sb₂) := by
      unfold barrierFn at hbarrier; linarith
    rw [hk]; exact le_of_lt this
  exact hcost k hsd hPhi

theorem jumpFront_bounded {K_max : ℕ} (sb : ShellBudget K_max)
    (Φ ν : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, jumpFront sb ≤ N ∨ barrierFn sb Φ ν < 0 := by
  obtain ⟨N, hN⟩ := barrier_eventually_negative Φ ν hν
  by_cases h : N ≤ jumpFront sb
  · exact ⟨N, Or.inr (by unfold barrierFn; exact hN (jumpFront sb) h)⟩
  · exact ⟨N, Or.inl (by omega)⟩

#check @jumpFront_realized_of_pos
#check @no_advance_past_barrier
#check @jumpFront_bounded

-- ============================================================
-- SECTION 5: PRODUCTION CAP AND DISSIPATION DOMINANCE
-- ============================================================

/-- Each shell's production is bounded by a finite drive Φ. -/
def ProductionCapped {K_max : ℕ} (sb : ShellBudget K_max) (Φ : ℝ) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ Φ

/-- Each shell's dissipation is at least the k⁴ barrier. -/
def DissipationDominates {K_max : ℕ} (sb : ShellBudget K_max) (ν : ℝ) : Prop :=
  ∀ k : Fin K_max, k4Cost ν k.val ≤ sb.D k

/-- Core contradiction: if P(k) > D(k) but also P(k) ≤ Φ ≤ νk⁴ ≤ D(k),
    we get D(k) < P(k) ≤ Φ ≤ νk⁴ ≤ D(k), contradiction. -/
theorem hcost_of_bounds {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν : ℝ)
    (hP : ProductionCapped sb Φ)
    (hD : DissipationDominates sb ν) :
    ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False := by
  intro k hsd hPhi
  have hPk : sb.P k ≤ Φ := hP k
  have hDk : k4Cost ν k.val ≤ sb.D k := hD k
  linarith

/-- **SELF-CONTAINED NO-ADVANCE THEOREM:**
    Under production cap and dissipation dominance,
    if the barrier is negative, no corridor advance is possible.
    No external hypotheses needed beyond the physical bounds. -/
theorem no_advance_past_barrier_of_bounds {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max) (Φ ν : ℝ)
    (hbarrier : barrierFn sb₂ Φ ν < 0)
    (hP : ProductionCapped sb₂ Φ)
    (hD : DissipationDominates sb₂ ν) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_past_barrier sb₁ sb₂ Φ ν hbarrier
  exact hcost_of_bounds sb₂ Φ ν hP hD

#check @hcost_of_bounds
#check @no_advance_past_barrier_of_bounds


-- ============================================================
-- SECTION 6: WEIGHTED VERSION
-- ============================================================

/-- Shell weight profile W(k), representing |v̂_k|² or similar. -/
def WeightProfile (K_max : ℕ) := Fin K_max → ℝ

/-- Weighted production cap: P(k) ≤ Φ · W(k). -/
def ProductionWeighted {K_max : ℕ} (sb : ShellBudget K_max) (Φ : ℝ)
    (W : WeightProfile K_max) : Prop :=
  ∀ k, sb.P k ≤ Φ * W k

/-- Weighted dissipation dominance: ν·k⁴·W(k) ≤ D(k). -/
def DissipationWeighted {K_max : ℕ} (sb : ShellBudget K_max) (ν : ℝ)
    (W : WeightProfile K_max) : Prop :=
  ∀ k, k4Cost ν k.val * W k ≤ sb.D k

/-- Weights are nonnegative. -/
def WeightNonneg {K_max : ℕ} (W : WeightProfile K_max) : Prop :=
  ∀ k, 0 ≤ W k

/-- Weighted cost contradiction: if D(k) < P(k) but also
    P(k) ≤ Φ·W(k) and ν·k⁴·W(k) ≤ D(k) and Φ ≤ ν·k⁴,
    then D(k) < P(k) ≤ Φ·W(k) ≤ ν·k⁴·W(k) ≤ D(k). -/
theorem hcost_of_weighted_bounds {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν : ℝ)
    (W : WeightProfile K_max)
    (hW : WeightNonneg W)
    (hP : ProductionWeighted sb Φ W)
    (hD : DissipationWeighted sb ν W) :
    ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False := by
  intro k hsd hPhi
  have hPk : sb.P k ≤ Φ * W k := hP k
  have hDk : k4Cost ν k.val * W k ≤ sb.D k := hD k
  have hWk : 0 ≤ W k := hW k
  have : Φ * W k ≤ k4Cost ν k.val * W k := by
    exact mul_le_mul_of_nonneg_right hPhi hWk
  linarith

/-- **SELF-CONTAINED NO-ADVANCE (WEIGHTED VERSION):**
    Physics-faithful version using shell weights W(k).
    Under weighted production cap and dissipation dominance,
    no corridor advance past the k⁴ barrier is possible. -/
theorem no_advance_weighted {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max) (Φ ν : ℝ)
    (W : WeightProfile K_max)
    (hbarrier : barrierFn sb₂ Φ ν < 0)
    (hW : WeightNonneg W)
    (hP : ProductionWeighted sb₂ Φ W)
    (hD : DissipationWeighted sb₂ ν W) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_past_barrier sb₁ sb₂ Φ ν hbarrier
  exact hcost_of_weighted_bounds sb₂ Φ ν W hW hP hD

#check @hcost_of_weighted_bounds
#check @no_advance_weighted

/-- A shellwise drive amplitude A(sb), to be instantiated later
    by a physical quantity such as ‖S‖∞ or ‖∇v‖∞. -/
def DriveAmplitude (K_max : ℕ) := ShellBudget K_max → ℝ

/-- A shellwise weight profile depending on the current budget,
    e.g. W_sb(k) ≈ |v̂_k|². -/
def WeightField (K_max : ℕ) := ShellBudget K_max → Fin K_max → ℝ

/-- Nonnegativity of the time-local shell weight. -/
def WeightFieldNonneg {K_max : ℕ} (W : WeightField K_max) : Prop :=
  ∀ sb k, 0 ≤ W sb k

/-- Physical production closure:
    P(k) ≤ A(sb) · k² · W(sb,k). -/
def ProductionK2Weighted {K_max : ℕ}
    (sb : ShellBudget K_max) (A : DriveAmplitude K_max) (W : WeightField K_max) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ A sb * (k.val : ℝ) ^ 2 * W sb k

/-- Physical dissipation closure:
    ν · k⁴ · W(sb,k) ≤ D(k). -/
def DissipationK4Weighted {K_max : ℕ}
    (sb : ShellBudget K_max) (ν : ℝ) (W : WeightField K_max) : Prop :=
  ∀ k : Fin K_max, ν * (k.val : ℝ) ^ 4 * W sb k ≤ sb.D k

/-- k²-vs-k⁴ contradiction:
    if D(k) < P(k), but P(k) ≤ A·k²·W and ν·k⁴·W ≤ D(k),
    then once A ≤ ν·k², contradiction follows. -/
theorem hcost_of_k2k4_bounds {K_max : ℕ}
    (sb : ShellBudget K_max) (ν : ℝ)
    (A : DriveAmplitude K_max) (W : WeightField K_max)
    (hW : WeightFieldNonneg W)
    (hP : ProductionK2Weighted sb A W)
    (hD : DissipationK4Weighted sb ν W) :
    ∀ k : Fin K_max,
      sb.D k < sb.P k →
      A sb ≤ ν * (k.val : ℝ) ^ 2 →
      False := by
  intro k hsd hA
  have hPk : sb.P k ≤ A sb * (k.val : ℝ) ^ 2 * W sb k := hP k
  have hDk : ν * (k.val : ℝ) ^ 4 * W sb k ≤ sb.D k := hD k
  have hWk : 0 ≤ W sb k := hW sb k
  have hAkW : A sb * (k.val : ℝ) ^ 2 * W sb k ≤
      ν * (k.val : ℝ) ^ 4 * W sb k := by
    have hfac_nonneg : 0 ≤ (k.val : ℝ) ^ 2 * W sb k := by positivity
    have h1 : A sb * ((k.val : ℝ) ^ 2 * W sb k) ≤
        (ν * (k.val : ℝ) ^ 2) * ((k.val : ℝ) ^ 2 * W sb k) :=
      mul_le_mul_of_nonneg_right hA hfac_nonneg
    linarith [show A sb * ((k.val : ℝ) ^ 2 * W sb k) =
        A sb * (k.val : ℝ) ^ 2 * W sb k from by ring,
      show (ν * (k.val : ℝ) ^ 2) * ((k.val : ℝ) ^ 2 * W sb k) =
        ν * (k.val : ℝ) ^ 4 * W sb k from by ring]
  linarith

/-- **SELF-CONTAINED NO-ADVANCE (k² vs k⁴ PHYSICAL VERSION):**
    If production grows at most like A·k²·W and dissipation dominates like ν·k⁴·W,
    then once A(sb₂) ≤ ν · jumpFront(sb₂)², no corridor advance is possible. -/
theorem no_advance_k2k4_weighted {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max) (ν : ℝ)
    (A : DriveAmplitude K_max) (W : WeightField K_max)
    (hAbarrier : A sb₂ ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hW : WeightFieldNonneg W)
    (hP : ProductionK2Weighted sb₂ A W)
    (hD : DissipationK4Weighted sb₂ ν W) :
    ¬ corridorStep sb₁ sb₂ := by
  intro hstep
  have hpos : 0 < jumpFront sb₂ := lt_of_le_of_lt (Nat.zero_le _) hstep
  obtain ⟨k, hsd, hk⟩ := jumpFront_realized_of_pos sb₂ hpos
  have hA : A sb₂ ≤ ν * (k.val : ℝ) ^ 2 := by
    have : (k.val : ℝ) = (jumpFront sb₂ : ℝ) := by exact_mod_cast hk
    rw [this]
    exact hAbarrier
  exact hcost_of_k2k4_bounds sb₂ ν A W hW hP hD k hsd hA

#check @hcost_of_k2k4_bounds
#check @no_advance_k2k4_weighted

-- ============================================================
-- SECTION 7: TIME-INDEXED TRAJECTORIES
-- ============================================================

/-- A discrete-time trajectory of shell budgets. -/
def BudgetTrajectory (K_max : ℕ) := ℕ → ShellBudget K_max

/-- Eventually, no corridor step can occur (weighted version). -/
theorem eventually_no_corridorStep_weighted {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Φ ν : ℝ)
    (W : WeightProfile K_max)
    (hW : WeightNonneg W)
    (hbarrier :
      ∃ Nb : ℕ, ∀ n : ℕ, Nb ≤ n → barrierFn (traj (n + 1)) Φ ν < 0)
    (hP :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n → ProductionWeighted (traj (n + 1)) Φ W)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n → DissipationWeighted (traj (n + 1)) ν W) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ corridorStep (traj n) (traj (n + 1)) := by
  rcases hbarrier with ⟨Nb, hb⟩
  rcases hP with ⟨Np, hp⟩
  rcases hD with ⟨Nd, hd⟩
  refine ⟨max Nb (max Np Nd), ?_⟩
  intro n hn
  have hNb : Nb ≤ n := le_trans (le_max_left Nb (max Np Nd)) hn
  have hmid : max Np Nd ≤ n := le_trans (le_max_right Nb (max Np Nd)) hn
  have hNp : Np ≤ n := le_trans (le_max_left Np Nd) hmid
  have hNd : Nd ≤ n := le_trans (le_max_right Np Nd) hmid
  apply no_advance_weighted (traj n) (traj (n + 1)) Φ ν W
  · exact hb n hNb
  · exact hW
  · exact hp n hNp
  · exact hd n hNd

/-- **FRONT EVENTUALLY NONINCREASING:**
    After the barrier regime begins, the jump front cannot increase. -/
theorem jumpFront_eventually_nonincreasing_weighted {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Φ ν : ℝ)
    (W : WeightProfile K_max)
    (hW : WeightNonneg W)
    (hbarrier :
      ∃ Nb : ℕ, ∀ n : ℕ, Nb ≤ n → barrierFn (traj (n + 1)) Φ ν < 0)
    (hP :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n → ProductionWeighted (traj (n + 1)) Φ W)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n → DissipationWeighted (traj (n + 1)) ν W) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      jumpFront (traj (n + 1)) ≤ jumpFront (traj n) := by
  rcases eventually_no_corridorStep_weighted traj Φ ν W hW hbarrier hP hD with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hnc : ¬ corridorStep (traj n) (traj (n + 1)) := hN n hn
  exact not_lt.mp hnc

#check @eventually_no_corridorStep_weighted
#check @jumpFront_eventually_nonincreasing_weighted


-- ============================================================
-- SECTION 8: EVENTUAL STABILIZATION
-- ============================================================

/-- A nonincreasing nat-valued sequence is bounded above by any earlier value. -/
theorem nonincreasing_tail_le
    (f : Nat → Nat)
    (hmono : ∀ n, f (n + 1) ≤ f n) :
    ∀ {m n : Nat}, m ≤ n → f n ≤ f m := by
  intro m n hmn
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep : f (m + k + 1) ≤ f (m + k) := by
        simpa [Nat.add_assoc] using hmono (m + k)
      exact le_trans hstep (ih le_self_add)

/-- If a nonincreasing nat-valued sequence is eventually bounded by `B`,
    then it eventually stabilizes. -/
theorem nat_seq_eventually_constant_from_bound
    (f : Nat → Nat)
    (N B : Nat)
    (hmono : ∀ n, f (n + 1) ≤ f n)
    (hbound : ∀ n, N ≤ n → f n ≤ B) :
    ∃ m, ∃ N', ∀ n, N' ≤ n → f n = m := by
  induction B generalizing N with
  | zero =>
      refine ⟨0, N, ?_⟩
      intro n hn
      have hle : f n ≤ 0 := hbound n hn
      omega
  | succ B ih =>
      by_cases hconst : ∀ n, N ≤ n → f n = B.succ
      · refine ⟨B.succ, N, ?_⟩
        intro n hn
        exact hconst n hn
      · push Not at hconst
        rcases hconst with ⟨N1, hN1, hneq⟩
        have hle1 : f N1 ≤ B := by
          have hle : f N1 ≤ B.succ := hbound N1 hN1
          omega
        have hbound' : ∀ n, N1 ≤ n → f n ≤ B := by
          intro n hn
          have htail : f n ≤ f N1 := nonincreasing_tail_le f hmono hn
          exact le_trans htail hle1
        exact ih N1 hbound'

/-- A nonincreasing nat-valued sequence eventually stabilizes. -/
theorem nat_seq_eventually_constant_of_nonincreasing
    (f : Nat → Nat)
    (hmono : ∀ n, f (n + 1) ≤ f n) :
    ∃ m, ∃ N, ∀ n, N ≤ n → f n = m := by
  apply nat_seq_eventually_constant_from_bound f 0 (f 0) hmono
  intro n hn
  exact nonincreasing_tail_le f hmono hn

#check @nonincreasing_tail_le
#check @nat_seq_eventually_constant_from_bound
#check @nat_seq_eventually_constant_of_nonincreasing

-- ============================================================
-- SECTION 9: FRONT EVENTUAL CONSTANT STABILIZATION
-- ============================================================

/-- **FRONT EVENTUALLY CONSTANT (WEIGHTED VERSION):**
    Under the weighted barrier regime, the jump front eventually stabilizes
    to a constant value. -/
theorem jumpFront_eventually_constant_weighted {K_max : ℕ}
    (traj : BudgetTrajectory K_max)
    (Φ ν : ℝ)
    (W : WeightProfile K_max)
    (hW : WeightNonneg W)
    (hbarrier :
      ∃ Nb : ℕ, ∀ n : ℕ, Nb ≤ n → barrierFn (traj (n + 1)) Φ ν < 0)
    (hP :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n → ProductionWeighted (traj (n + 1)) Φ W)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n → DissipationWeighted (traj (n + 1)) ν W) :
    ∃ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → jumpFront (traj n) = m := by
  rcases
    jumpFront_eventually_nonincreasing_weighted
      traj Φ ν W hW hbarrier hP hD with
    ⟨N0, hmono⟩
  let f : ℕ → ℕ := fun n => jumpFront (traj (N0 + n))
  have hfmono : ∀ n, f (n + 1) ≤ f n := by
    intro n
    have hN0 : N0 ≤ N0 + n := by omega
    simpa [f, Nat.add_assoc] using hmono (N0 + n) hN0
  rcases nat_seq_eventually_constant_of_nonincreasing f hfmono with
    ⟨m, N1, hconst⟩
  refine ⟨m, N0 + N1, ?_⟩
  intro n hn
  have hN0 : N0 ≤ n := by omega
  rcases Nat.exists_eq_add_of_le hN0 with ⟨t, rfl⟩
  have ht : N1 ≤ t := by omega
  simpa [f] using hconst t ht

#check @jumpFront_eventually_constant_weighted

-- ============================================================
-- SECTION 10: PHYSICAL PRODUCTION CLOSURE
-- ============================================================

/-- A shell-energy profile E(sb,k), intended to model shell energy
    such as Σ_{|κ|≈k} |v̂(κ)|². -/
def ShellEnergy (K_max : ℕ) := ShellBudget K_max → Fin K_max → ℝ

/-- Nonnegativity of shell energy. -/
def ShellEnergyNonneg {K_max : ℕ} (E : ShellEnergy K_max) : Prop :=
  ∀ sb k, 0 ≤ E sb k

/-- A strain amplitude, intended to model ‖S‖∞ or a comparable
    stretching drive amplitude. -/
def StrainAmplitude (K_max : ℕ) := ShellBudget K_max → ℝ

/-- Physical shellwise production closure:
    P(k) ≤ A(sb) · k² · E(sb,k). -/
def PhysicalProductionClosure {K_max : ℕ}
    (sb : ShellBudget K_max)
    (A : StrainAmplitude K_max)
    (E : ShellEnergy K_max) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ A sb * (k.val : ℝ) ^ 2 * E sb k

/-- Physical shellwise dissipation closure:
    ν · k⁴ · E(sb,k) ≤ D(k). -/
def PhysicalDissipationClosure {K_max : ℕ}
    (sb : ShellBudget K_max)
    (ν : ℝ)
    (E : ShellEnergy K_max) : Prop :=
  ∀ k : Fin K_max, ν * (k.val : ℝ) ^ 4 * E sb k ≤ sb.D k

/-- Physical contradiction lemma:
    if shellwise production is controlled by A·k²·E and dissipation by ν·k⁴·E,
    then any stretching-dominated shell must satisfy A(sb) > ν·k². -/
theorem physical_hcost_of_closure {K_max : ℕ}
    (sb : ShellBudget K_max) (ν : ℝ)
    (A : StrainAmplitude K_max) (E : ShellEnergy K_max)
    (hE : ShellEnergyNonneg E)
    (hP : PhysicalProductionClosure sb A E)
    (hD : PhysicalDissipationClosure sb ν E) :
    ∀ k : Fin K_max,
      sb.D k < sb.P k →
      A sb ≤ ν * (k.val : ℝ) ^ 2 →
      False := by
  intro k hsd hA
  have hPk : sb.P k ≤ A sb * (k.val : ℝ) ^ 2 * E sb k := hP k
  have hDk : ν * (k.val : ℝ) ^ 4 * E sb k ≤ sb.D k := hD k
  have hEk : 0 ≤ E sb k := hE sb k
  have hk2_nonneg : 0 ≤ (k.val : ℝ) ^ 2 := by positivity
  have hfac_nonneg : 0 ≤ (k.val : ℝ) ^ 2 * E sb k := by
    nlinarith
  have hAE : A sb * (k.val : ℝ) ^ 2 * E sb k ≤
      ν * (k.val : ℝ) ^ 4 * E sb k := by
    have h1 :
        A sb * ((k.val : ℝ) ^ 2 * E sb k) ≤
        (ν * (k.val : ℝ) ^ 2) * ((k.val : ℝ) ^ 2 * E sb k) :=
      mul_le_mul_of_nonneg_right hA hfac_nonneg
    linarith [show A sb * ((k.val : ℝ) ^ 2 * E sb k) =
        A sb * (k.val : ℝ) ^ 2 * E sb k from by ring,
      show (ν * (k.val : ℝ) ^ 2) * ((k.val : ℝ) ^ 2 * E sb k) =
        ν * (k.val : ℝ) ^ 4 * E sb k from by ring]
  linarith

/-- Physical no-advance theorem:
    once the strain amplitude is below the shellwise k²-threshold at the front,
    the front cannot advance. -/
theorem no_advance_physical {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max) (ν : ℝ)
    (A : StrainAmplitude K_max) (E : ShellEnergy K_max)
    (hAbarrier : A sb₂ ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hE : ShellEnergyNonneg E)
    (hP : PhysicalProductionClosure sb₂ A E)
    (hD : PhysicalDissipationClosure sb₂ ν E) :
    ¬ corridorStep sb₁ sb₂ := by
  intro hstep
  have hpos : 0 < jumpFront sb₂ := lt_of_le_of_lt (Nat.zero_le _) hstep
  obtain ⟨k, hsd, hk⟩ := jumpFront_realized_of_pos sb₂ hpos
  have hkR : (k.val : ℝ) = (jumpFront sb₂ : ℝ) := by
    exact_mod_cast hk
  have hA : A sb₂ ≤ ν * (k.val : ℝ) ^ 2 := by
    rw [hkR]
    exact hAbarrier
  exact physical_hcost_of_closure sb₂ ν A E hE hP hD k hsd hA

#check @ShellEnergy
#check @ShellEnergyNonneg
#check @StrainAmplitude
#check @PhysicalProductionClosure
#check @PhysicalDissipationClosure
#check @physical_hcost_of_closure
#check @no_advance_physical

-- ============================================================
-- SECTION 11: PHYSICAL INSTANTIATION FROM STRAIN SUP
-- ============================================================

/-- A shellwise vorticity-energy profile Ξ(sb,k), intended to model
    ‖ω_k‖²_{L²} or a comparable shellwise vorticity quantity. -/
def ShellVorticitySq (K_max : ℕ) := ShellBudget K_max → Fin K_max → ℝ

/-- A strain-sup amplitude, intended to model ‖S‖∞ or a comparable
    stretching drive amplitude. -/
def StrainSup (K_max : ℕ) := ShellBudget K_max → ℝ

/-- Nonnegativity of the strain-sup amplitude. -/
def StrainSupNonneg {K_max : ℕ} (Ssup : StrainSup K_max) : Prop :=
  ∀ sb, 0 ≤ Ssup sb

/-- Physical interface assumption:
    shellwise production is controlled by strain-sup times shellwise vorticity size,
    i.e. P(k) ≤ ‖S‖∞ · Ξ(k). -/
def physical_production_from_strain_sup {K_max : ℕ}
    (sb : ShellBudget K_max)
    (Ssup : StrainSup K_max)
    (Xi : ShellVorticitySq K_max) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ Ssup sb * Xi sb k

/-- Physical interface assumption:
    shellwise vorticity size is controlled by shell energy,
    i.e. Ξ(k) ≤ C_shell · k² · E(k). -/
def shell_vorticity_energy_bound {K_max : ℕ}
    (Xi : ShellVorticitySq K_max)
    (E : ShellEnergy K_max)
    (C_shell : ℝ) : Prop :=
  ∀ sb k, Xi sb k ≤ C_shell * (k.val : ℝ) ^ 2 * E sb k

/-- The induced strain amplitude A(sb) = C_shell · ‖S‖∞(sb). -/
def inducedStrainAmplitude {K_max : ℕ}
    (Ssup : StrainSup K_max)
    (C_shell : ℝ) : StrainAmplitude K_max :=
  fun sb => Ssup sb * C_shell

/-- Instantiation of `PhysicalProductionClosure` from the two physical interface
    assumptions:
      P(k) ≤ ‖S‖∞ · Ξ(k),    Ξ(k) ≤ C_shell · k² · E(k).
    Hence P(k) ≤ (C_shell · ‖S‖∞) · k² · E(k). -/
theorem physical_production_closure_inst {K_max : ℕ}
    (sb : ShellBudget K_max)
    (Ssup : StrainSup K_max)
    (Xi : ShellVorticitySq K_max)
    (E : ShellEnergy K_max)
    (C_shell : ℝ)
    (hS : StrainSupNonneg Ssup)
    (_hC : 0 ≤ C_shell)
    (hprod : physical_production_from_strain_sup sb Ssup Xi)
    (hXiE : shell_vorticity_energy_bound Xi E C_shell) :
    PhysicalProductionClosure sb (inducedStrainAmplitude Ssup C_shell) E := by
  intro k
  have hPk : sb.P k ≤ Ssup sb * Xi sb k := hprod k
  have hXi : Xi sb k ≤ C_shell * (k.val : ℝ) ^ 2 * E sb k := hXiE sb k
  have hSsb : 0 ≤ Ssup sb := hS sb
  have hmul :
      Ssup sb * Xi sb k ≤
        Ssup sb * (C_shell * (k.val : ℝ) ^ 2 * E sb k) := by
    exact mul_le_mul_of_nonneg_left hXi hSsb
  calc
    sb.P k ≤ Ssup sb * Xi sb k := hPk
    _ ≤ Ssup sb * (C_shell * (k.val : ℝ) ^ 2 * E sb k) := hmul
    _ = inducedStrainAmplitude Ssup C_shell sb * (k.val : ℝ) ^ 2 * E sb k := by
        unfold inducedStrainAmplitude
        ring

/-- Physical instantiation of the no-advance theorem:
    if shellwise production is controlled by strain-sup,
    shellwise vorticity is controlled by shell energy,
    and dissipation has the ν·k⁴·E lower bound,
    then once C_shell · ‖S‖∞ is below the front threshold, no corridor advance
    is possible. -/
theorem no_advance_physical_inst {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (ν C_shell : ℝ)
    (Ssup : StrainSup K_max)
    (Xi : ShellVorticitySq K_max)
    (E : ShellEnergy K_max)
    (hAbarrier :
      inducedStrainAmplitude Ssup C_shell sb₂ ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hS : StrainSupNonneg Ssup)
    (hC : 0 ≤ C_shell)
    (hE : ShellEnergyNonneg E)
    (hprod : physical_production_from_strain_sup sb₂ Ssup Xi)
    (hXiE : shell_vorticity_energy_bound Xi E C_shell)
    (hD : PhysicalDissipationClosure sb₂ ν E) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical sb₁ sb₂ ν (inducedStrainAmplitude Ssup C_shell) E
  · exact hAbarrier
  · exact hE
  · exact physical_production_closure_inst sb₂ Ssup Xi E C_shell hS hC hprod hXiE
  · exact hD

#check @ShellVorticitySq
#check @StrainSup
#check @StrainSupNonneg
#check @physical_production_from_strain_sup
#check @shell_vorticity_energy_bound
#check @inducedStrainAmplitude
#check @physical_production_closure_inst
#check @no_advance_physical_inst
