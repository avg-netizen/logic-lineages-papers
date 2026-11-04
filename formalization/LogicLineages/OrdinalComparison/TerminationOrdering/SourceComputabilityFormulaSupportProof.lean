module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticOperatorsSupportProof

def numeral {α : Type} : Nat → OrdinaryArithmetic.Term α
  | 0 => OrdinaryArithmetic.zeroTerm
  | k+1 => OrdinaryArithmetic.succTerm (numeral k)

theorem numeralTruth {α : Type} (k : Nat) (v : α → Nat) : (numeral k).realize v = k := by
  induction k with
  | zero => rfl
  | succ k ih => change (numeral k).realize v + 1 = k+1; rw [ih]

def allOne {α : Type} (p : language.Formula (α ⊕ Fin 1)) : language.Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) p).alls

def existsOne {α : Type} (p : language.Formula (α ⊕ Fin 1)) : language.Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) p).exs

theorem allOneTruth {α : Type} (p : language.Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) :
    realize P (allOne p) v ↔ ∀ xs : Fin 1 → Nat, realize P p (Sum.elim v xs) := by
  letI := naturalStructure P
  change (BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) p).alls.Realize v ↔ _
  rw [BoundedFormula.realize_alls]
  apply forall_congr'
  intro xs
  rw [BoundedFormula.realize_relabel]
  simpa only [Function.comp_id, Function.comp_def, id_eq, Fin.castAdd_zero, Fin.cast_eq_self, realize] using
    (Formula.boundedFormula_realize_eq_realize p (Sum.elim v xs) (xs ∘ Fin.natAdd 1))

theorem existsOneTruth {α : Type} (p : language.Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) :
    realize P (existsOne p) v ↔ ∃ xs : Fin 1 → Nat, realize P p (Sum.elim v xs) := by
  letI := naturalStructure P
  change (BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) p).exs.Realize v ↔ _
  rw [BoundedFormula.realize_exs]
  apply exists_congr
  intro xs
  rw [BoundedFormula.realize_relabel]
  simpa only [Function.comp_id, Function.comp_def, id_eq, Fin.castAdd_zero, Fin.cast_eq_self, realize] using
    (Formula.boundedFormula_realize_eq_realize p (Sum.elim v xs) (xs ∘ Fin.natAdd 1))

theorem generalConjTruth {α : Type} (p q : language.Formula α) (P : Nat → Prop) (v : α → Nat) :
    realize P (p ⊓ q) v ↔ realize P p v ∧ realize P q v := by
  letI := naturalStructure P
  exact Formula.realize_inf

theorem generalImpTruth {α : Type} (p q : language.Formula α) (P : Nat → Prop) (v : α → Nat) :
    realize P (p.imp q) v ↔ (realize P p v → realize P q v) := by
  letI := naturalStructure P
  rfl

theorem generalRelabelTruth {α β : Type} (p : language.Formula α) (g : α → β)
    (P : Nat → Prop) (v : β → Nat) :
    realize P (p.relabel g) v ↔ realize P p (v ∘ g) := by
  letI := naturalStructure P
  exact Formula.realize_relabel

theorem arithmeticSubstTruth {α β : Type} (p : OrdinaryArithmetic.Formula α)
    (ts : α → OrdinaryArithmetic.Term β) (P : Nat → Prop) (v : β → Nat) :
    realize P (arithmeticEmbedding.onFormula (p.subst ts)) v ↔
      p.Realize (fun i => (ts i).realize v) := by
  rw [embeddingTruth]
  simp only [Formula.Realize, BoundedFormula.realize_subst]

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
