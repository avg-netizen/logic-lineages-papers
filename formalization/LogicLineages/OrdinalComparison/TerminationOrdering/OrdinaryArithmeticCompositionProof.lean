module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionProof

open FirstOrder Language OrdinaryArithmetic OrdinaryArithmeticCompositionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem relabeledTruth {α : Type} {k : Nat} (p : Formula (α ⊕ Fin k))
    (v : α → Nat) (xs : Fin k → Nat) :
    (BoundedFormula.relabel (id : α ⊕ Fin k → α ⊕ Fin k) p).Realize v xs ↔
      p.Realize (Sum.elim v xs) := by
  rw [BoundedFormula.realize_relabel]
  simpa only [Function.comp_id, Function.comp_def, id_eq, Fin.castAdd_zero,
    Fin.cast_eq_self] using
    (Formula.boundedFormula_realize_eq_realize p (Sum.elim v xs) (xs ∘ Fin.natAdd k))

theorem existsFiniteTruth {α : Type} {k : Nat}
    (p : Formula (α ⊕ Fin k)) (v : α → Nat) :
    (existsFin p).Realize v ↔ ∃ xs : Fin k → Nat, p.Realize (Sum.elim v xs) := by
  rw [existsFin, BoundedFormula.realize_exs]
  exact exists_congr (fun xs => relabeledTruth p v xs)

theorem forallFiniteTruth {α : Type} {k : Nat}
    (p : Formula (α ⊕ Fin k)) (v : α → Nat) :
    (forallFin p).Realize v ↔ ∀ xs : Fin k → Nat, p.Realize (Sum.elim v xs) := by
  rw [forallFin, BoundedFormula.realize_alls]
  exact forall_congr' (fun xs => relabeledTruth p v xs)

theorem applyGraphTruth {n : Nat} {α : Type}
    (p : Formula (Fin (n + 1))) (out : Term α) (inputs : Fin n → Term α) (v : α → Nat) :
    (applyGraph p out inputs).Realize v ↔
      p.Realize (Fin.cons (out.realize v) (fun i => (inputs i).realize v)) := by
  simp only [applyGraph, Formula.Realize]
  rw [BoundedFormula.realize_subst]
  have h : (fun j : Fin (n + 1) => (Fin.cases out inputs j : Term α).realize v) =
      Fin.cons (out.realize v) (fun i => (inputs i).realize v) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  rw [h]

theorem finiteConjunctionTruth {α : Type} {n : Nat}
    (p : Fin n → Formula α) (v : α → Nat) :
    (andFin p).Realize v ↔ ∀ i, (p i).Realize v := by
  simp only [andFin, Formula.Realize]
  rw [BoundedFormula.realize_foldr_inf]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

theorem lessTruth : LessTruth := by
  intro α s t v
  rw [lessFormula, existsFiniteTruth]
  simp only [Formula.realize_equal, OrdinaryArithmeticBetaProof.realize_add,
    OrdinaryArithmeticBetaProof.realize_succ, Term.realize_relabel, Term.realize_var,
    Sum.elim_comp_inl, Sum.elim_inr]
  constructor
  · rintro ⟨xs, h⟩
    omega
  · intro h
    refine ⟨fun _ => t.realize v - (s.realize v + 1), ?_⟩
    change s.realize v + (t.realize v - (s.realize v + 1) + 1) = t.realize v
    omega

theorem actualCompositionGraph : ActualCompositionGraph := by
  intro m n f g F G hf hg v
  rw [compositionGraph, existsFiniteTruth]
  simp only [Formula.realize_inf, applyGraphTruth, finiteConjunctionTruth,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  simp only [hf, hg, Fin.cons_succ, Fin.cons_zero]
  constructor
  · rintro ⟨xs, hf', hg'⟩
    have hx : xs = fun i => evaluate (g i) (List.Vector.ofFn (fun j => v j.succ)) := by
      funext i
      exact (hg' i).symm
    simpa only [evaluate, hx] using hf'
  · intro h
    refine ⟨fun i => evaluate (g i) (List.Vector.ofFn (fun j => v j.succ)), ?_, ?_⟩
    · exact h
    · intro i
      rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionProof
