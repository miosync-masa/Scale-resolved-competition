import NSBarrier.NSFiniteSource
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace NSFiniteSourceClosure

open NSFiniteSource

/-- Total production on a finite set of shells. -/
noncomputable def shellProductionSource {K_max : ℕ}
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) : ℝ :=
  S.sum (fun k => sb.P k)

/-- Total dissipation on a finite set of shells. -/
noncomputable def shellDissipationSource {K_max : ℕ}
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) : ℝ :=
  S.sum (fun k => sb.D k)

#check @shellProductionSource
#check @shellDissipationSource

/-- The net source on a shell set is bounded above by its total production. -/
theorem shellNet_le_shellProductionSource {K_max : ℕ}
    (sb : ShellBudget K_max) (S : Finset (Fin K_max)) :
    shellNetSource sb S ≤ shellProductionSource sb S := by
  unfold shellNetSource shellProductionSource
  refine Finset.sum_le_sum ?_
  intro k hk
  have hD : 0 ≤ sb.D k := sb.D_nonneg k
  linarith

#check @shellNet_le_shellProductionSource

/-- If on a finite low-shell set one has the ratio bound `P_k ≤ M D_k`,
    then total production on that set is bounded by `M` times total dissipation. -/
theorem finite_shell_closure_of_ratio_bound {K_max : ℕ}
    (sb : ShellBudget K_max) (M : ℝ) (N : ℕ)
    (_hM : 0 ≤ M)
    (hratio : ∀ k : Fin K_max, k.val < N → sb.P k ≤ M * sb.D k) :
    shellProductionSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N))
      ≤
    M * shellDissipationSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) := by
  unfold shellProductionSource shellDissipationSource
  calc
    ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < N), sb.P k
      ≤
    ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < N), M * sb.D k := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact hratio k (Finset.mem_filter.mp hk).2
    _ = M * ∑ k ∈ Finset.univ.filter (fun k : Fin K_max => k.val < N), sb.D k := by
        symm
        rw [Finset.mul_sum]

#check @finite_shell_closure_of_ratio_bound

/-- If all shells above `N` are dissipative, then the total net source
    is controlled by the low-shell net source below `N`. -/
theorem finite_source_reduction_of_cutoff {K_max : ℕ}
    (sb : ShellBudget K_max) (N : ℕ)
    (htail : ∀ k : Fin K_max, N ≤ k.val → sb.P k ≤ sb.D k) :
    shellNetSource sb Finset.univ
      ≤
    shellNetSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) := by
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
    refine Finset.sum_nonpos ?_
    intro k hk
    have hkge : N ≤ k.val := Nat.not_lt.mp ((Finset.mem_filter.mp hk).2)
    have hpd : sb.P k ≤ sb.D k := htail k hkge
    linarith
  linarith [hsplit, htail_nonpos]

#check @finite_source_reduction_of_cutoff

/-- **FINITE SOURCE CLOSURE OF CUTOFF**:
    if high shells are dissipative and low shells satisfy a bounded ratio
    `P_k ≤ M D_k`, then the total net shell source is controlled by the
    low-shell dissipation with coefficient `M`. -/
theorem finite_source_closure_of_cutoff {K_max : ℕ}
    (sb : ShellBudget K_max) (M : ℝ) (N : ℕ)
    (hM : 0 ≤ M)
    (htail : ∀ k : Fin K_max, N ≤ k.val → sb.P k ≤ sb.D k)
    (hratio : ∀ k : Fin K_max, k.val < N → sb.P k ≤ M * sb.D k) :
    shellNetSource sb Finset.univ
      ≤
    M * shellDissipationSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) := by
  have hred :
      shellNetSource sb Finset.univ
        ≤
      shellNetSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) :=
    finite_source_reduction_of_cutoff sb N htail
  have hnet_prod :
      shellNetSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N))
        ≤
      shellProductionSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) :=
    shellNet_le_shellProductionSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N))
  have hprod_closure :
      shellProductionSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N))
        ≤
      M * shellDissipationSource sb (Finset.univ.filter (fun k : Fin K_max => k.val < N)) :=
    finite_shell_closure_of_ratio_bound sb M N hM hratio
  exact le_trans hred (le_trans hnet_prod hprod_closure)

#check @finite_source_closure_of_cutoff

/-- **FINITE SOURCE CLOSURE OF BARRIER**:
    specialize the previous cutoff theorem to the canonical barrier cutoff
    extracted from `tail_dissipative_of_barrier`. -/
theorem finite_source_closure_of_barrier {K_max : ℕ}
    (sb : ShellBudget K_max) (Φ ν M : ℝ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hbar :
      ∀ k : Fin K_max, sb.D k < sb.P k → Φ ≤ k4Cost ν k.val → False)
    (hratio :
      ∀ k : Fin K_max,
        k.val < Classical.choose (tail_dissipative_of_barrier sb Φ ν hν hbar) →
          sb.P k ≤ M * sb.D k) :
    shellNetSource sb Finset.univ
      ≤
    M * shellDissipationSource sb
      (Finset.univ.filter
        (fun k : Fin K_max =>
          k.val < Classical.choose (tail_dissipative_of_barrier sb Φ ν hν hbar))) := by
  let N : ℕ := Classical.choose (tail_dissipative_of_barrier sb Φ ν hν hbar)
  have htail : ∀ k : Fin K_max, N ≤ k.val → sb.P k ≤ sb.D k := by
    simpa [N] using
      (Classical.choose_spec (tail_dissipative_of_barrier sb Φ ν hν hbar))
  have hratioN : ∀ k : Fin K_max, k.val < N → sb.P k ≤ M * sb.D k := by
    simpa [N] using hratio
  simpa [N] using
    (finite_source_closure_of_cutoff sb M N hM htail hratioN)

#check @finite_source_closure_of_barrier

end NSFiniteSourceClosure
