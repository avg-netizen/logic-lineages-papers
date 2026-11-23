module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOddProgressiveInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof PositiveArithmeticPredicateSubstitution
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst membershipSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst impSubst)
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)
open NumberedWindowInternalDirectSourcePartitionRawTargets (rawSourceCheck observePartition)
open NumberedWindowInternalOddProgressiveInductionProof (oddLower)

/-- The result quantifies the actual union code, under the original packed
append and accepted observer. The parameters are the ordered components. -/
def consequence {α : Type} (count : Program 2) (a b : OTerm α) : Formula α :=
  allOne ((unionGraph count (a.relabel Sum.inl) (b.relabel Sum.inl)
    (.var (.inr (0 : Fin 1)))).imp (membership true (.var (.inr (0 : Fin 1)))))

/-- Own right membership is part of the inner motive, not assumed at the
current right node before odd induction. -/
def innerState {α : Type} (count : Program 2) (a b : OTerm α) : Formula α :=
  membership true b ⊓ consequence count a b

def innerMotive {α : Type} (count : Program 2) (a : OTerm α) : Formula (α ⊕ Fin 1) :=
  innerState count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))

/-- The open lower-state formula on the actual right edge, with the left
parameter fixed. This is the literal opened inner motive. -/
def innerLower {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (a b : OTerm α) : Formula α :=
  allOne ((edge data true c (b.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (innerState count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))))

theorem unionGraphSubst {α β : Type} (count : Program 2) (a b u : OTerm α)
    (ts : α → OTerm β) :
    (unionGraph count a b u).subst (fun i => emb (ts i)) =
      unionGraph count (a.subst ts) (b.subst ts) (u.subst ts) :=
  acceptsSubst (rawSourceCheck (observePartition count)) u a b ts

theorem consequenceSubst {α β : Type} (count : Program 2) (a b : OTerm α)
    (ts : α → OTerm β) :
    (consequence count a b).subst (fun i => emb (ts i)) =
      consequence count (a.subst ts) (b.subst ts) := by
  simp only [consequence,allEmbeddedSubst,impSubst,unionGraphSubst,membershipSubst,liftTermSubst] <;> rfl

theorem innerStateSubst {α β : Type} (count : Program 2) (a b : OTerm α)
    (ts : α → OTerm β) :
    (innerState count a b).subst (fun i => emb (ts i)) =
      innerState count (a.subst ts) (b.subst ts) := by
  change (membership true b).subst _ ⊓ (consequence count a b).subst _ = _
  rw [membershipSubst,consequenceSubst] <;> rfl

theorem innerLowerSubst {α β : Type} (data : Data) (c : Nat) (count : Program 2)
    (a b : OTerm α) (ts : α → OTerm β) :
    (innerLower data c count a b).subst (fun i => emb (ts i)) =
      innerLower data c count (a.subst ts) (b.subst ts) := by
  simp only [innerLower,allEmbeddedSubst,impSubst,edgeSubst,innerStateSubst,liftTermSubst] <;> rfl

theorem innerStateRename {α β : Type} (count : Program 2) (a b : OTerm α) (j : α → β) :
    (innerState count a b).relabel j = innerState count (a.relabel j) (b.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (innerState count a b).subst (fun i => emb (.var (j i))) = _
  rw [innerStateSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem innerLowerRename {α β : Type} (data : Data) (c : Nat) (count : Program 2)
    (a b : OTerm α) (j : α → β) :
    (innerLower data c count a b).relabel j =
      innerLower data c count (a.relabel j) (b.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (innerLower data c count a b).subst (fun i => emb (.var (j i))) = _
  rw [innerLowerSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem innerMotiveAt {α : Type} (count : Program 2) (a b : OTerm α) :
    instantiate (innerMotive count a) (emb b) = innerState count a b := by
  rw [innerMotive,instantiate,bindEmbedding,innerStateSubst,liftBind,varBind]

theorem innerLowerAt {α : Type} (data : Data) (c : Nat) (count : Program 2) (a b y : OTerm α) :
    instantiate ((edge data true c (b.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (innerState count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1))))) (emb y) =
        (edge data true c b y).imp (innerState count a y) := by
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,innerStateSubst,liftBind,varBind]

theorem literalOddLower {α : Type} (data : Data) (c : Nat) (count : Program 2) (a : OTerm α) :
    oddLower data c (.var (.inr (0 : Fin 1))) (innerMotive count a) =
      innerLower data c count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1))) := by
  have h : liftPredicateFormula (innerMotive count a) =
      innerState count ((a.relabel Sum.inl).relabel Sum.inl) (.var (.inr (0 : Fin 1))) := by
    rw [liftPredicateFormula,innerMotive,innerStateRename]
    simp only [Term.relabel_relabel] <;> rfl
  unfold oddLower innerLower
  rw [h]

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerSyntaxProof
