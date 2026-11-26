module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open OriginalHereditaryValidityInternalPushSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundSubst weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open InternalStrongInduction
theorem atPayloadSubst {α β : Type} (leaf : Program 2) (payload : OTerm α) (ts : α → OTerm β) :
    (AtPayload leaf payload).subst (fun a => emb (ts a)) =
      AtPayload leaf (payload.subst ts) := by
  unfold AtPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCompletionSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atPayloadRename {α β : Type} (leaf : Program 2) (payload : OTerm α) (j : α → β) :
    (AtPayload leaf payload).relabel j =
      AtPayload leaf (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtPayload leaf payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]


theorem payloadMatrixWitness {α : Type} (leaf : Program 2) (payload input parameter : OTerm α) :
    (payloadMatrix leaf payload).subst
      (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        (HasCompletion leaf input parameter payload) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCompletionSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl


def payloadPredicate (leaf : Program 2) {α : Type} : Formula (α ⊕ Fin 1) :=
  AtPayload leaf (.var (.inr 0))


def belowPayload {α : Type} (leaf : Program 2) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (payloadPredicate leaf) payload


theorem payloadPredicateInstantiate {α : Type} (leaf : Program 2) (payload : OTerm α) :
    instantiate (payloadPredicate leaf) (emb payload) =
      AtPayload leaf payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]


@[simp] theorem belowPayloadRename {α β : Type} (leaf : Program 2) (payload : OTerm α) (j : α → β) :
    (belowPayload leaf payload).relabel j =
      belowPayload leaf (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl


theorem payloadPredicateLift {α : Type} (leaf : Program 2) :
    lift (payloadPredicate leaf (α := α)) =
      payloadPredicate leaf (α := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
