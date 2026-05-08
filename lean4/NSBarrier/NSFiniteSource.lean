import NSBarrier.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace NSFiniteSource

/-- Net shell source on a finite set of shells:
    `∑ (P_k - D_k)`. -/
noncomputable def shellNetSource {K_max : ℕ}
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) : ℝ :=
  S.sum (fun k => sb.P k - sb.D k)

/-- Once the `k^4` barrier excludes stretching-dominated shells above a threshold,
    every sufficiently high shell is dissipative:
    `P_k ≤ D_k` for all large enough `k`. -/
theorem tail_dissipative_of_barrier {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν : ℝ)
    (hν : 0 < ν)
    (hbar :
      ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False) :
    ∃ N : ℕ, ∀ k : Fin K_max, N ≤ k.val → sb.P k ≤ sb.D k := by
  obtain ⟨N, hN⟩ := barrier_eventually_negative Φ ν hν
  refine ⟨N, ?_⟩
  intro k hkN
  by_cases hsd : sb.D k < sb.P k
  · exfalso
    have hPhi : Φ ≤ k4Cost ν k.val := by
      have hneg : Φ - k4Cost ν k.val < 0 := hN k.val hkN
      linarith
    exact hbar k hsd hPhi
  · linarith

/-- Equivalent form: all stretching-dominated shells lie below a finite cutoff. -/
theorem activeShells_below_of_barrier {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν : ℝ)
    (hν : 0 < ν)
    (hbar :
      ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False) :
    ∃ N : ℕ, ∀ k : Fin K_max, k ∈ activeShells sb → k.val < N := by
  obtain ⟨N, htail⟩ := tail_dissipative_of_barrier sb Φ ν hν hbar
  refine ⟨N, ?_⟩
  intro k hk
  by_contra hknot
  have hkge : N ≤ k.val := Nat.not_lt.mp hknot
  have hsd : sb.D k < sb.P k := (Finset.mem_filter.mp hk).2
  have hpd : sb.P k ≤ sb.D k := htail k hkge
  linarith

/-- **FINITE SOURCE REDUCTION OF BARRIER**:
    once the `k^4` barrier is active, the total shellwise net source
    is controlled by finitely many low shells. -/
theorem finite_source_reduction_of_barrier {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν : ℝ)
    (hν : 0 < ν)
    (hbar :
      ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False) :
    ∃ N : ℕ,
      shellNetSource sb Finset.univ
        ≤
      shellNetSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) := by
  obtain ⟨N, htail⟩ := tail_dissipative_of_barrier sb Φ ν hν hbar
  refine ⟨N, ?_⟩
  have hsplit :
      shellNetSource sb Finset.univ =
        shellNetSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N))
          +
        ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => ¬ k.val < N),
          (sb.P k - sb.D k) := by
    unfold shellNetSource
    symm
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun k : Fin K_max => k.val < N)
        (f := fun k => sb.P k - sb.D k))
  have htail_nonpos :
      ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => ¬ k.val < N),
        (sb.P k - sb.D k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    have hkge : N ≤ k.val := Nat.not_lt.mp ((Finset.mem_filter.mp hk).2)
    have hpd : sb.P k ≤ sb.D k := htail k hkge
    linarith
  linarith [hsplit, htail_nonpos]

#check @shellNetSource
#check @tail_dissipative_of_barrier
#check @activeShells_below_of_barrier
#check @finite_source_reduction_of_barrier

end NSFiniteSource
