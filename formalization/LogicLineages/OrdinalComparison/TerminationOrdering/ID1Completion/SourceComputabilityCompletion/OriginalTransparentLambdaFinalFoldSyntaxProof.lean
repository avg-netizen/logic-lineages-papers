module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentLambdaFinalFold InternalParameterizedApplicationCertifiedResultFoldClosure InternalApplicationCertificateConstructors
open InternalStrongInduction
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
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

theorem commonFoldPSubst {α β : Type} (guard leaf valid : Program 2) (combine : Program 5)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (commonFoldP guard leaf valid combine out input parameter).subst (fun a => emb (ts a)) =
      commonFoldP guard leaf valid combine (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [commonFoldP,InternalParameterizedApplicationCertifiedResultFoldClosure.certifiedFoldP,conjunctionSubst,graph2,programSubst,consTermSubst,
    emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem commonFoldPRename {α β : Type} (guard leaf valid : Program 2)
    (combine : Program 5) (out input parameter : OTerm α) (j : α → β) :
    (commonFoldP guard leaf valid combine out input parameter).relabel j =
      commonFoldP guard leaf valid combine (out.relabel j) (input.relabel j)
        (parameter.relabel j) := by
  simp only [commonFoldP,conjunctionRename,certifiedFoldPRename,graph2Rename]

theorem hasCertifiedOutputSubst {α β : Type} (guard leaf valid : Program 2) (combine : Program 5) (input parameter : OTerm α) (ts : α → OTerm β) :
    (hasCertifiedOutputP guard leaf valid combine input parameter).subst (fun a => emb (ts a)) =
      hasCertifiedOutputP guard leaf valid combine (input.subst ts) (parameter.subst ts) := by
  unfold hasCertifiedOutputP
  rw [existsSubst,liftedEmbedding,commonFoldPSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem hasCertifiedOutputRename {α β : Type} (guard leaf valid : Program 2) (combine : Program 5) (input parameter : OTerm α) (j : α → β) :
    (hasCertifiedOutputP guard leaf valid combine input parameter).relabel j =
      hasCertifiedOutputP guard leaf valid combine (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (hasCertifiedOutputP guard leaf valid combine input parameter).subst
    (fun a => emb (.var (j a))) = _
  rw [hasCertifiedOutputSubst]
  simp only [← termRelabelAsSubst]


theorem commonFoldPInstantiate {α : Type} (guard leaf valid : Program 2) (combine : Program 5) (out input parameter : OTerm α) :
    instantiate (commonFoldP guard leaf valid combine (.var (.inr 0))
      (input.relabel Sum.inl) (parameter.relabel Sum.inl)) (emb out) =
      commonFoldP guard leaf valid combine out input parameter := by
  rw [instantiate,bindEmbedding,commonFoldPSubst]
  simp only [varBind,liftBind]


theorem atPayloadSubst {α β : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload : OTerm α) (ts : α → OTerm β) :
    (atPayloadP guard leaf valid combine payload).subst (fun a => emb (ts a)) =
      atPayloadP guard leaf valid combine (payload.subst ts) := by
  unfold atPayloadP payloadMatrixP
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCertifiedOutputSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atPayloadRename {α β : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload : OTerm α) (j : α → β) :
    (atPayloadP guard leaf valid combine payload).relabel j =
      atPayloadP guard leaf valid combine (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayloadP guard leaf valid combine payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]


theorem payloadMatrixWitness {α : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload input parameter : OTerm α) :
    (payloadMatrixP guard leaf valid combine payload).subst
      (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        (hasCertifiedOutputP guard leaf valid combine input parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrixP
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCertifiedOutputSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl


def payloadPredicate (guard leaf valid : Program 2) (combine : Program 5) {α : Type} : Formula (α ⊕ Fin 1) :=
  atPayloadP guard leaf valid combine (.var (.inr 0))


def belowPayload {α : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (payloadPredicate guard leaf valid combine) payload


theorem payloadPredicateInstantiate {α : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload : OTerm α) :
    instantiate (payloadPredicate guard leaf valid combine) (emb payload) =
      atPayloadP guard leaf valid combine payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]


@[simp] theorem belowPayloadRename {α β : Type} (guard leaf valid : Program 2) (combine : Program 5) (payload : OTerm α) (j : α → β) :
    (belowPayload guard leaf valid combine payload).relabel j =
      belowPayload guard leaf valid combine (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl


theorem payloadPredicateLift {α : Type} (guard leaf valid : Program 2) (combine : Program 5) :
    lift (payloadPredicate guard leaf valid combine (α := α)) =
      payloadPredicate guard leaf valid combine (α := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldSyntaxProof
