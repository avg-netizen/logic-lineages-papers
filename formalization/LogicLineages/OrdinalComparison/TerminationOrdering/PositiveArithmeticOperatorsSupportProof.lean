module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsSupportProof
open FirstOrder Language PositiveArithmeticOperators

theorem expansion (P : Nat → Prop) : letI := naturalStructure P; arithmeticEmbedding.IsExpansionOn Nat := by
  letI := naturalStructure P
  constructor
  · intro n f v
    cases f <;> rfl
  · intro n r v
    exact nomatch r

theorem embeddingTruth (α : Type) (phi : OrdinaryArithmetic.Formula α) (P : Nat → Prop) (v : α → Nat) :
    realize P (arithmeticEmbedding.onFormula phi) v ↔ phi.Realize v := by
  letI := naturalStructure P
  letI := expansion P
  exact arithmeticEmbedding.realize_onFormula phi

theorem predicateTruth {α : Type} (P : Nat → Prop) (t : OrdinaryArithmetic.Term α) (v : α → Nat) :
    realize P (Positive.predicate t).formula v ↔ P (t.realize v) := by
  letI := naturalStructure P
  letI := expansion P
  simp [realize,Positive.formula,Relations.formula₁,Relations.formula,
    Formula.Realize,Relations.boundedFormula,BoundedFormula.Realize,
    Term.realize_relabel,arithmeticEmbedding.realize_onTerm,naturalStructure]
  rfl

theorem conjTruth {α : Type} (P : Nat → Prop) (p q : Positive α) (v : α → Nat) :
    realize P (Positive.conj p q).formula v ↔ realize P p.formula v ∧ realize P q.formula v := by
  letI := naturalStructure P
  exact Formula.realize_inf

theorem guardedTruth {α : Type} (P : Nat → Prop) (g : OrdinaryArithmetic.Formula α) (p : Positive α) (v : α → Nat) :
    realize P (Positive.guarded g p).formula v ↔ (g.Realize v → realize P p.formula v) := by
  letI := naturalStructure P
  change ((arithmeticEmbedding.onFormula g).Realize v → p.formula.Realize v) ↔ _
  rw [← embeddingTruth α g P v]
  rfl

theorem allTruth {α : Type} (P : Nat → Prop) (p : Positive (α ⊕ Fin 1)) (v : α → Nat) :
    realize P (Positive.all p).formula v ↔ ∀ xs : Fin 1 → Nat, realize P p.formula (Sum.elim v xs) := by
  letI := naturalStructure P
  change (BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) p.formula).alls.Realize v ↔ _
  rw [BoundedFormula.realize_alls]
  apply forall_congr'
  intro xs
  rw [BoundedFormula.realize_relabel]
  simpa only [Function.comp_id,Function.comp_def,id_eq,Fin.castAdd_zero,Fin.cast_eq_self,realize] using
    (Formula.boundedFormula_realize_eq_realize p.formula (Sum.elim v xs) (xs ∘ Fin.natAdd 1))

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsSupportProof
