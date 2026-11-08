module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalResultFoldInvariant InternalApplicationCertificateConstructors
open InternalStrongInduction
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalBoundedDescentNormalizerSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem sourcePremisesSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (member : Program 1) (input typ : OTerm α) (ts : α → OTerm β) :
    (sourcePremises old member input typ).subst (fun a => emb (ts a)) =
      sourcePremises old member (input.subst ts) (typ.subst ts) := by
  simp only [sourcePremises,conjunctionSubst,validSubst,leftSubst]

theorem certifiedResultSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OTerm α) (ts : α → OTerm β) :
    (certifiedResult old representative member out input).subst (fun a => emb (ts a)) =
      certifiedResult old representative member (out.subst ts) (input.subst ts) := by
  simp only [certifiedResult,InternalApplicationCertifiedResultFoldClosure.certifiedFold,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem outputInvariantSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out typ : OTerm α) (ts : α → OTerm β) :
    (outputInvariant old representative member out typ).subst (fun a => emb (ts a)) =
      outputInvariant old representative member (out.subst ts) (typ.subst ts) := by
  simp only [outputInvariant,conjunctionSubst,validSubst,leftSubst,transitionSubst]

theorem certifiedOutputSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (ts : α → OTerm β) :
    (certifiedOutput old representative member out input typ).subst (fun a => emb (ts a)) =
      certifiedOutput old representative member (out.subst ts) (input.subst ts) (typ.subst ts) := by
  simp only [certifiedOutput,conjunctionSubst,certifiedResultSubst,outputInvariantSubst]

theorem foldGraphSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OTerm α) (ts : α → OTerm β) :
    (foldGraph old representative member out input).subst (fun a => emb (ts a)) =
      foldGraph old representative member (out.subst ts) (input.subst ts) := by
  simp only [foldGraph,graph1,programSubst,consTermSubst,emptySubst]

theorem goodRunAcceptedSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input : OTerm α) (ts : α → OTerm β) :
    (goodRunAccepted old representative member input).subst (fun a => emb (ts a)) =
      goodRunAccepted old representative member (input.subst ts) := by
  simp only [goodRunAccepted,graph1,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem successfulOutputSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (ts : α → OTerm β) :
    (successfulOutput old representative member out input typ).subst (fun a => emb (ts a)) =
      successfulOutput old representative member (out.subst ts) (input.subst ts) (typ.subst ts) := by
  simp only [successfulOutput,conjunctionSubst,goodRunAcceptedSubst,outputInvariantSubst]

theorem typedOutputSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (ts : α → OTerm β) :
    (typedOutput old representative member out input typ).subst (fun a => emb (ts a)) =
      typedOutput old representative member (out.subst ts) (input.subst ts) (typ.subst ts) := by
  simp only [typedOutput,conjunctionSubst,goodRunAcceptedSubst,InternalCanonicalDescentSelection.typedAccepted,graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem sourcePremisesRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (member : Program 1) (input typ : OTerm α) (j : α → β) :
    (sourcePremises old member input typ).relabel j = sourcePremises old member (input.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (sourcePremises old member input typ).subst (fun a => emb (.var (j a))) = _
  rw [sourcePremisesSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem certifiedResultRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OTerm α) (j : α → β) :
    (certifiedResult old representative member out input).relabel j = certifiedResult old representative member (out.relabel j) (input.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (certifiedResult old representative member out input).subst (fun a => emb (.var (j a))) = _
  rw [certifiedResultSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem outputInvariantRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out typ : OTerm α) (j : α → β) :
    (outputInvariant old representative member out typ).relabel j = outputInvariant old representative member (out.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (outputInvariant old representative member out typ).subst (fun a => emb (.var (j a))) = _
  rw [outputInvariantSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem certifiedOutputRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (j : α → β) :
    (certifiedOutput old representative member out input typ).relabel j = certifiedOutput old representative member (out.relabel j) (input.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (certifiedOutput old representative member out input typ).subst (fun a => emb (.var (j a))) = _
  rw [certifiedOutputSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem foldGraphRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OTerm α) (j : α → β) :
    (foldGraph old representative member out input).relabel j = foldGraph old representative member (out.relabel j) (input.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (foldGraph old representative member out input).subst (fun a => emb (.var (j a))) = _
  rw [foldGraphSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem goodRunAcceptedRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input : OTerm α) (j : α → β) :
    (goodRunAccepted old representative member input).relabel j = goodRunAccepted old representative member (input.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (goodRunAccepted old representative member input).subst (fun a => emb (.var (j a))) = _
  rw [goodRunAcceptedSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem successfulOutputRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (j : α → β) :
    (successfulOutput old representative member out input typ).relabel j = successfulOutput old representative member (out.relabel j) (input.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (successfulOutput old representative member out input typ).subst (fun a => emb (.var (j a))) = _
  rw [successfulOutputSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem typedOutputRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) (j : α → β) :
    (typedOutput old representative member out input typ).relabel j = typedOutput old representative member (out.relabel j) (input.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (typedOutput old representative member out input typ).subst (fun a => emb (.var (j a))) = _
  rw [typedOutputSubst]
  simp only [← termRelabelAsSubst]

theorem hasCertifiedOutputSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input typ : OTerm α) (ts : α → OTerm β) :
    (hasCertifiedOutput old representative member input typ).subst (fun a => emb (ts a)) =
      hasCertifiedOutput old representative member (input.subst ts) (typ.subst ts) := by
  unfold hasCertifiedOutput
  rw [existsSubst,liftedEmbedding,certifiedOutputSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem hasCertifiedOutputRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input typ : OTerm α) (j : α → β) :
    (hasCertifiedOutput old representative member input typ).relabel j =
      hasCertifiedOutput old representative member (input.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (hasCertifiedOutput old representative member input typ).subst
    (fun a => emb (.var (j a))) = _
  rw [hasCertifiedOutputSubst]
  simp only [← termRelabelAsSubst]

theorem certifiedOutputInstantiate {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α) :
    instantiate (certifiedOutput old representative member (.var (.inr 0))
      (input.relabel Sum.inl) (typ.relabel Sum.inl)) (emb out) =
      certifiedOutput old representative member out input typ := by
  rw [instantiate,bindEmbedding,certifiedOutputSubst]
  simp only [varBind,liftBind]

theorem atPayloadSubst {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α) (ts : α → OTerm β) :
    (atPayload old representative member payload).subst (fun a => emb (ts a)) =
      atPayload old representative member (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    sourcePremisesSubst,hasCertifiedOutputSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α) (j : α → β) :
    (atPayload old representative member payload).relabel j =
      atPayload old representative member (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload old representative member payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

theorem payloadMatrixWitness {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload input typ : OTerm α) :
    (payloadMatrix old representative member payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((sourcePremises old member input typ).imp
          (hasCertifiedOutput old representative member input typ)) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    sourcePremisesSubst,hasCertifiedOutputSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

/-- The induction predicate binds only the payload, not a fixed packed input. -/
def payloadPredicate (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) {α : Type} : Formula (α ⊕ Fin 1) :=
  atPayload old representative member (.var (.inr 0))

def belowPayload {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (payloadPredicate old representative member) payload

theorem payloadPredicateInstantiate {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α) :
    instantiate (payloadPredicate old representative member) (emb payload) =
      atPayload old representative member payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α) (j : α → β) :
    (belowPayload old representative member payload).relabel j =
      belowPayload old representative member (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) :
    lift (payloadPredicate old representative member (α := α)) =
      payloadPredicate old representative member (α := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantSyntaxProof
