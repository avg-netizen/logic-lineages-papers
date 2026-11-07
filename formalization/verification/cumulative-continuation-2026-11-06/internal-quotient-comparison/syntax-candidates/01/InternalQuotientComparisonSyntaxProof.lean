module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalQuotientComparison
open InternalTagArithmeticSyntaxProof InternalBinderTransportSyntaxProof
open InternalTermSubstitutionSyntaxProof InternalSourceInversionSupportProof
open InternalGraphCompositionSyntaxProof InternalOriginalOrderSyntaxProof
open InternalDerivationRenamingSyntaxProof

/-- Arbitrary ordinary term substitution in the original existential order formula. -/
theorem originalOrderSubst {α β : Type} (s t : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.lessFormula s t).subst ts =
      OrdinaryArithmetic.lessFormula (s.subst ts) (t.subst ts) := by
  have ht (u : OrdinaryArithmetic.Term α) :
      (u.relabel (Sum.inl : α → α ⊕ Fin 1)).subst
        (Sum.elim (fun x => (ts x).relabel Sum.inl) (fun i => .var (.inr i))) =
      (u.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]
    rfl
  unfold OrdinaryArithmetic.lessFormula
  rw [existsFinSubst,equalitySubstitution]
  simp only [OrdinaryArithmetic.addTerm,OrdinaryArithmetic.succTerm,
    applyTwoSubstitution,applyOneSubstitution,ht,Term.subst,Sum.elim_inr]

theorem orderSubst {α β : Type} (s t : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (ltF s t).subst (fun x => emb (ts x)) = ltF (s.subst ts) (t.subst ts) := by
  unfold ltF
  rw [← embedSubst,originalOrderSubst]

theorem orderInstantiate {α : Type} (s t : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (u : OrdinaryArithmetic.Term α) :
    instantiate (ltF s t) (emb u) = ltF (s.subst (bindTerm u)) (t.subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding,orderSubst]

theorem orderSuccessor {α : Type} (s t : OrdinaryArithmetic.Term (α ⊕ Fin 1)) :
    successorInstance (ltF s t) = ltF (s.subst nextTerm) (t.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,orderSubst]

theorem comparisonSubst {α β : Type} (s t : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (comparison s t).subst (fun x => emb (ts x)) = comparison (s.subst ts) (t.subst ts) := by
  unfold comparison
  simp only [onEquality]
  change (ltF s t).subst (fun x => emb (ts x)) ⊔
    ((eqn s t).subst (fun x => emb (ts x)) ⊔ (ltF t s).subst (fun x => emb (ts x))) = _
  rw [orderSubst,eqnSubst,orderSubst]
  rfl

theorem comparisonInstantiate {α : Type} (s t : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (u : OrdinaryArithmetic.Term α) :
    instantiate (comparison s t) (emb u) = comparison (s.subst (bindTerm u)) (t.subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding,comparisonSubst]

theorem comparisonSuccessor {α : Type} (s t : OrdinaryArithmetic.Term (α ⊕ Fin 1)) :
    successorInstance (comparison s t) = comparison (s.subst nextTerm) (t.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,comparisonSubst]

theorem comparisonRename {α β : Type} (s t : OrdinaryArithmetic.Term α) (j : α → β) :
    (comparison s t).relabel j = comparison (s.relabel j) (t.relabel j) := by
  unfold comparison
  simp only [onEquality]
  change (ltF s t).relabel j ⊔ ((eqn s t).relabel j ⊔ (ltF t s).relabel j) = _
  rw [orderRename,eqnRelabel,orderRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
