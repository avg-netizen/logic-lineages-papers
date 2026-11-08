module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultFoldTotality InternalParameterizedApplicationCertifiedResultFoldClosure InternalApplicationCertificateConstructors
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

theorem certifiedFoldPSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (certifiedFoldP guard leaf combine out input parameter).subst (fun a => emb (ts a)) =
      certifiedFoldP guard leaf combine (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [certifiedFoldP,conjunctionSubst,graph2,programSubst,consTermSubst,
    emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem foldGraphSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5) (out input parameter : OTerm α) (ts : α → OTerm β) :
    (foldGraphP guard leaf combine out input parameter).subst (fun a => emb (ts a)) =
      foldGraphP guard leaf combine (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [foldGraphP,graph2,programSubst,consTermSubst,emptySubst]


theorem goodRunAcceptedSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5) (input parameter : OTerm α) (ts : α → OTerm β) :
    (goodRunAcceptedP guard leaf combine input parameter).subst (fun a => emb (ts a)) =
      goodRunAcceptedP guard leaf combine (input.subst ts) (parameter.subst ts) := by
  simp only [goodRunAcceptedP,graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]


@[simp] theorem foldGraphRename {α β : Type} (guard leaf : Program 2) (combine : Program 5) (out input parameter : OTerm α) (j : α → β) :
    (foldGraphP guard leaf combine out input parameter).relabel j = foldGraphP guard leaf combine (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (foldGraphP guard leaf combine out input parameter).subst (fun a => emb (.var (j a))) = _
  rw [foldGraphSubst]
  simp only [← termRelabelAsSubst]


@[simp] theorem goodRunAcceptedRename {α β : Type} (guard leaf : Program 2) (combine : Program 5) (input parameter : OTerm α) (j : α → β) :
    (goodRunAcceptedP guard leaf combine input parameter).relabel j = goodRunAcceptedP guard leaf combine (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (goodRunAcceptedP guard leaf combine input parameter).subst (fun a => emb (.var (j a))) = _
  rw [goodRunAcceptedSubst]
  simp only [← termRelabelAsSubst]


theorem hasCertifiedOutputSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5) (input parameter : OTerm α) (ts : α → OTerm β) :
    (hasCertifiedOutputP guard leaf combine input parameter).subst (fun a => emb (ts a)) =
      hasCertifiedOutputP guard leaf combine (input.subst ts) (parameter.subst ts) := by
  unfold hasCertifiedOutputP
  rw [existsSubst,liftedEmbedding,certifiedFoldPSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem hasCertifiedOutputRename {α β : Type} (guard leaf : Program 2) (combine : Program 5) (input parameter : OTerm α) (j : α → β) :
    (hasCertifiedOutputP guard leaf combine input parameter).relabel j =
      hasCertifiedOutputP guard leaf combine (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (hasCertifiedOutputP guard leaf combine input parameter).subst
    (fun a => emb (.var (j a))) = _
  rw [hasCertifiedOutputSubst]
  simp only [← termRelabelAsSubst]


theorem certifiedFoldPInstantiate {α : Type} (guard leaf : Program 2) (combine : Program 5) (out input parameter : OTerm α) :
    instantiate (certifiedFoldP guard leaf combine (.var (.inr 0))
      (input.relabel Sum.inl) (parameter.relabel Sum.inl)) (emb out) =
      certifiedFoldP guard leaf combine out input parameter := by
  rw [instantiate,bindEmbedding,certifiedFoldPSubst]
  simp only [varBind,liftBind]


theorem atPayloadSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α) (ts : α → OTerm β) :
    (atPayloadP guard leaf combine payload).subst (fun a => emb (ts a)) =
      atPayloadP guard leaf combine (payload.subst ts) := by
  unfold atPayloadP payloadMatrixP
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCertifiedOutputSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atPayloadRename {α β : Type} (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α) (j : α → β) :
    (atPayloadP guard leaf combine payload).relabel j =
      atPayloadP guard leaf combine (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayloadP guard leaf combine payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]


theorem payloadMatrixWitness {α : Type} (guard leaf : Program 2) (combine : Program 5) (payload input parameter : OTerm α) :
    (payloadMatrixP guard leaf combine payload).subst
      (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        (hasCertifiedOutputP guard leaf combine input parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrixP
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCertifiedOutputSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl


def payloadPredicate (guard leaf : Program 2) (combine : Program 5) {α : Type} : Formula (α ⊕ Fin 1) :=
  atPayloadP guard leaf combine (.var (.inr 0))


def belowPayload {α : Type} (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (payloadPredicate guard leaf combine) payload


theorem payloadPredicateInstantiate {α : Type} (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α) :
    instantiate (payloadPredicate guard leaf combine) (emb payload) =
      atPayloadP guard leaf combine payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]


@[simp] theorem belowPayloadRename {α β : Type} (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α) (j : α → β) :
    (belowPayload guard leaf combine payload).relabel j =
      belowPayload guard leaf combine (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl


theorem payloadPredicateLift {α : Type} (guard leaf : Program 2) (combine : Program 5) :
    lift (payloadPredicate guard leaf combine (α := α)) =
      payloadPredicate guard leaf combine (α := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
