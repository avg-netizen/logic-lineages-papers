module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentDecoderValidatorCollapseInduction InternalParameterizedApplicationCertifiedResultFoldClosure InternalApplicationCertificateConstructors
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

theorem acceptanceSubst {α β : Type} (left right : Program 2)
    (raw parameter : OTerm α) (ts : α → OTerm β) :
    (Acceptance left right raw parameter).subst (fun a => emb (ts a)) =
      Acceptance left right (raw.subst ts) (parameter.subst ts) := by
  simp only [Acceptance,Formula.iff,BoundedFormula.iff,conjunctionSubst,impSubst,graph2,
    programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]

@[simp] theorem acceptanceRename {α β : Type} (left right : Program 2)
    (raw parameter : OTerm α) (j : α → β) :
    (Acceptance left right raw parameter).relabel j =
      Acceptance left right (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Acceptance left right raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [acceptanceSubst]
  simp only [← termRelabelAsSubst]

theorem atPayloadSubst {α β : Type} (left right : Program 2) (payload : OTerm α) (ts : α → OTerm β) :
    (atPayload left right payload).subst (fun a => emb (ts a)) =
      atPayload left right (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    acceptanceSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atPayloadRename {α β : Type} (left right : Program 2) (payload : OTerm α) (j : α → β) :
    (atPayload left right payload).relabel j =
      atPayload left right (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload left right payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]


theorem payloadMatrixWitness {α : Type} (left right : Program 2) (payload input parameter : OTerm α) :
    (payloadMatrix left right payload).subst
      (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        (Acceptance left right input parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    acceptanceSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl


theorem payloadPredicateInstantiate {α : Type} (left right : Program 2) (payload : OTerm α) :
    instantiate (payloadPredicate left right) (emb payload) =
      atPayload left right payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]


@[simp] theorem belowPayloadRename {α β : Type} (left right : Program 2) (payload : OTerm α) (j : α → β) :
    (belowPayload left right payload).relabel j =
      belowPayload left right (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl


theorem payloadPredicateLift {α : Type} (left right : Program 2) :
    lift (payloadPredicate left right (alpha := α)) =
      payloadPredicate left right (alpha := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
