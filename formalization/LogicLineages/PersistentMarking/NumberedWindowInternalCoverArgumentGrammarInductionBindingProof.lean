module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (lift)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind zSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalGraphCompositionSyntaxProof (bindSubst exsSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (numeralSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalPairing (pairing)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

attribute [local irreducible] programGraph
variable {α β : Type}

private theorem pairSubst (p d w : OTerm α) (ts : α → OTerm β) :
    (codePair p d w).subst (fun a => emb (ts a)) = codePair (p.subst ts) (d.subst ts) (w.subst ts) := by
  have tape : (fun i : Fin 2 => ((![d,w] : Fin 2 → OTerm α) i).subst ts) = ![d.subst ts,w.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  change (programGraph pairing p ![d,w]).subst _ = _
  rw [programSubst,tape]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (ts : α → Term β) :
    (block phi).subst ts = block (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem payloadSubst (F : Program 1) (s : Settings) (q : OTerm α)
    (vals : Fin 6 → OTerm α) (ts : α → OTerm β) :
    (argumentPayload F s q vals).subst (fun a => emb (ts a)) =
      argumentPayload F s (q.subst ts) (fun i => (vals i).subst ts) := by
  simp only [argumentPayload,conjunctionSubst,unarySubst,pairSubst,observedSubst,memberSubst,
    headsTerm,typesTerm,numeralSubst]

theorem argumentExistsSubst (F : Program 1) (s : Settings) (q : OTerm α) (ts : α → OTerm β) :
    (argumentExists F s q).subst (fun a => emb (ts a)) = argumentExists F s (q.subst ts) := by
  unfold argumentExists argumentMatrix
  rw [blockSubst,liftedEmbedding,payloadSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem argumentExistsRename (F : Program 1) (s : Settings) (q : OTerm α) (j : α → β) :
    (argumentExists F s q).relabel j = argumentExists F s (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (argumentExists F s q).subst (fun x => emb (.var (j x))) = _
  rw [argumentExistsSubst,← termRelabelAsSubst]

theorem argumentWitness (F : Program 1) (s : Settings) (q : OTerm α) (vals : Fin 6 → OTerm α) :
    (argumentMatrix F s q).subst (Sum.elim Term.var (fun i => emb (vals i))) =
      argumentPayload F s q vals := by
  have he : Sum.elim Term.var (fun i => emb (vals i)) = (fun x => emb (Sum.elim Term.var vals x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold argumentMatrix
  rw [payloadSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

private theorem atSubst (F G : Program 1) (s : Settings) (q : OTerm α) (ts : α → OTerm β) :
    (argumentAt F G s q).subst (fun a => emb (ts a)) = argumentAt F G s (q.subst ts) := by
  simp only [argumentAt,impSubst,argumentExistsSubst,unarySubst,zSubst]

theorem argumentAtRename (F G : Program 1) (s : Settings) (q : OTerm α) (j : α → β) :
    (argumentAt F G s q).relabel j = argumentAt F G s (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (argumentAt F G s q).subst (fun x => emb (.var (j x))) = _
  rw [atSubst,← termRelabelAsSubst]

theorem argumentMotiveAt (F G : Program 1) (s : Settings) (q : OTerm α) :
    instantiate (argumentMotive F G s) (emb q) = argumentAt F G s q := by
  simp only [instantiate,bindEmbedding,argumentMotive,atSubst,varBind]

theorem argumentMotiveLift (F G : Program 1) (s : Settings) :
    lift (argumentMotive (α := α) F G s) = argumentMotive (α := α ⊕ Fin 1) F G s := by
  unfold lift argumentMotive
  rw [argumentAtRename]
  rfl

#print axioms argumentExistsSubst
#print axioms argumentWitness
#print axioms argumentMotiveAt
#print axioms argumentMotiveLift

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
