module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerProgressProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterSyntaxProof
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
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalCertifiedUnionInnerSyntaxProof (consequence consequenceSubst)
open NumberedWindowInternalOddProgressiveInductionProof (oddLower)

/-- Quantify the right component before the original union observation. -/
def outerClaim {α : Type} (count : Program 2) (a : OTerm α) : Formula α :=
  allOne ((membership true (.var (.inr (0 : Fin 1)))).imp
    (consequence count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))))

def outerState {α : Type} (count : Program 2) (a : OTerm α) : Formula α :=
  membership true a ⊓ outerClaim count a

def outerMotive {α : Type} (count : Program 2) : Formula (α ⊕ Fin 1) :=
  outerState count (.var (.inr (0 : Fin 1)))

def outerLower {α : Type} (data : Data) (c : Nat) (count : Program 2) (a : OTerm α) : Formula α :=
  allOne ((edge data true c (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (outerState count (.var (.inr (0 : Fin 1)))))

theorem outerClaimSubst {α β : Type} (count : Program 2) (a : OTerm α) (ts : α → OTerm β) :
    (outerClaim count a).subst (fun i => emb (ts i)) = outerClaim count (a.subst ts) := by
  simp only [outerClaim,allEmbeddedSubst,impSubst,membershipSubst,consequenceSubst,liftTermSubst] <;> rfl

theorem outerStateSubst {α β : Type} (count : Program 2) (a : OTerm α) (ts : α → OTerm β) :
    (outerState count a).subst (fun i => emb (ts i)) = outerState count (a.subst ts) := by
  change (membership true a).subst _ ⊓ (outerClaim count a).subst _ = _
  rw [membershipSubst,outerClaimSubst] <;> rfl

theorem outerLowerSubst {α β : Type} (data : Data) (c : Nat) (count : Program 2)
    (a : OTerm α) (ts : α → OTerm β) :
    (outerLower data c count a).subst (fun i => emb (ts i)) = outerLower data c count (a.subst ts) := by
  simp only [outerLower,allEmbeddedSubst,impSubst,edgeSubst,outerStateSubst,liftTermSubst] <;> rfl

theorem outerStateRename {α β : Type} (count : Program 2) (a : OTerm α) (j : α → β) :
    (outerState count a).relabel j = outerState count (a.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (outerState count a).subst (fun i => emb (.var (j i))) = _
  rw [outerStateSubst,← termRelabelAsSubst]

theorem outerLowerRename {α β : Type} (data : Data) (c : Nat) (count : Program 2)
    (a : OTerm α) (j : α → β) :
    (outerLower data c count a).relabel j = outerLower data c count (a.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (outerLower data c count a).subst (fun i => emb (.var (j i))) = _
  rw [outerLowerSubst,← termRelabelAsSubst]

theorem outerMotiveAt {α : Type} (count : Program 2) (a : OTerm α) :
    instantiate (outerMotive (α := α) count) (emb a) = outerState count a := by
  rw [outerMotive,instantiate,bindEmbedding,outerStateSubst,varBind]

theorem outerClaimAt {α : Type} (count : Program 2) (a b : OTerm α) :
    instantiate ((membership true (.var (.inr (0 : Fin 1)))).imp
      (consequence count (a.relabel Sum.inl) (.var (.inr (0 : Fin 1))))) (emb b) =
        (membership true b).imp (consequence count a b) := by
  simp only [instantiate,bindEmbedding,impSubst,membershipSubst,consequenceSubst,liftBind,varBind]

theorem outerLowerAt {α : Type} (data : Data) (c : Nat) (count : Program 2) (a y : OTerm α) :
    instantiate ((edge data true c (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (outerState count (.var (.inr (0 : Fin 1))))) (emb y) =
        (edge data true c a y).imp (outerState count y) := by
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,outerStateSubst,liftBind,varBind]

theorem literalOuterOddLower {α : Type} (data : Data) (c : Nat) (count : Program 2) :
    oddLower data c (.var (.inr (0 : Fin 1))) (outerMotive (α := α) count) =
      outerLower data c count (.var (.inr (0 : Fin 1))) := by
  have h : liftPredicateFormula (outerMotive (α := α) count) =
      outerState count (.var (.inr (0 : Fin 1))) := by
    rw [liftPredicateFormula,outerMotive,outerStateRename] <;> rfl
  unfold oddLower outerLower
  rw [h]

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterSyntaxProof
