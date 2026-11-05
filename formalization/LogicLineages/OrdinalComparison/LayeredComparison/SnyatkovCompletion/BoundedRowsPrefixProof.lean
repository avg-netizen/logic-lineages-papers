module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphExistentialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsPrefixProof
open NormalForm BoundedRows

theorem boundAtom_eval (i bound : Nat) (ν : Nat → Nat) :
    (Formula.atom (.nonnegative (boundRow i bound))).eval ν ↔ ν i < bound := by
  simp only [Formula.eval, Atom.eval, boundRow, rowValue, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Summand.term, Term.value,
    neg_one_mul, add_zero]
  omega

theorem boundsFormula_eval (bounds : List (Nat × Nat)) (ν : Nat → Nat) :
    (boundsFormula bounds).eval ν ↔ ∀ entry ∈ bounds, ν entry.1 < entry.2 := by
  induction bounds with
  | nil => simp [boundsFormula, Formula.eval]
  | cons entry rest ih =>
      change ((Formula.atom (.nonnegative (boundRow entry.1 entry.2))).eval ν ∧
        (boundsFormula rest).eval ν) ↔ _
      simp only [boundAtom_eval, ih, List.mem_cons, forall_eq_or_imp]

/-- A duplicate-free bounded prefix chooses one final valuation satisfying
every original bound. No change is allowed outside the listed names. -/
theorem boundedPrefix_iff_frame (bounds : List (Nat × Nat))
    (hd : (bounds.map Prod.fst).Nodup) (ν : Nat → Nat) (p : Formula) :
    boundedPrefix ν bounds p ↔ ∃ σ : Nat → Nat,
      (∀ i, i ∉ bounds.map Prod.fst → σ i = ν i) ∧
      (∀ entry ∈ bounds, σ entry.1 < entry.2) ∧ p.eval σ := by
  induction bounds generalizing ν with
  | nil =>
      constructor
      · intro hp
        exact ⟨ν, fun _ _ => rfl, by simp, hp⟩
      · rintro ⟨σ, hframe, _, hp⟩
        have he : σ = ν := funext (fun i => hframe i (by simp))
        subst σ
        exact hp
  | cons entry rest ih =>
      rcases entry with ⟨j, bound⟩
      have hnd := List.nodup_cons.mp hd
      constructor
      · rintro ⟨n, hn, hp⟩
        obtain ⟨σ, hframe, hbounds, hbody⟩ :=
          (ih hnd.2 (Function.update ν j n)).mp hp
        have hj : σ j = n := by
          simpa only [Function.update_self] using hframe j hnd.1
        refine ⟨σ, ?_, ?_, hbody⟩
        · intro i hi
          have hrest : i ∉ rest.map Prod.fst := fun h => hi (List.mem_cons_of_mem j h)
          have hne : i ≠ j := by
            intro he
            apply hi
            simp only [List.map_cons, List.mem_cons, he, true_or]
          rw [hframe i hrest, Function.update_of_ne hne]
        · intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            simpa only [hj] using hn
          · exact hbounds entry he
      · rintro ⟨σ, hframe, hbounds, hbody⟩
        refine ⟨σ j, hbounds (j, bound) (List.mem_cons_self), ?_⟩
        apply (ih hnd.2 (Function.update ν j (σ j))).mpr
        refine ⟨σ, ?_, fun entry he => hbounds entry (List.mem_cons_of_mem _ he), hbody⟩
        intro i hi
        by_cases hne : i = j
        · subst i
          simp only [Function.update_self]
        · rw [Function.update_of_ne hne]
          apply hframe i
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨hne, hi⟩

theorem exactExistingPrefix : BoundedRowsTargets.ExactExistingPrefix := by
  intro bounds hd p ν
  rw [BoundedRowsSemanticProof.actualBlockElimination bounds p ν,
    boundedPrefix_iff_frame bounds hd ν p,
    SourceTermGraphExistentialProof.existsPrefix_iff_frame]
  constructor
  · rintro ⟨σ, hframe, hbounds, hp⟩
    exact ⟨σ, hframe, (boundsFormula_eval bounds σ).mpr hbounds, hp⟩
  · rintro ⟨σ, hframe, hbounds, hp⟩
    exact ⟨σ, hframe, (boundsFormula_eval bounds σ).mp hbounds, hp⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsPrefixProof
