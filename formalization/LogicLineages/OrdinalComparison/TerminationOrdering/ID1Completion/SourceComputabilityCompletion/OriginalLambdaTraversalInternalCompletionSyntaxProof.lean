module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionSyntaxProof
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

open OriginalLambdaTraversalInternalCompletion

theorem completesSubst {α β : Type} (leaf : Program 2)
    (value parameter count produced : OTerm α) (ts : α → OTerm β) :
    (Completes leaf value parameter count produced).subst (fun a => emb (ts a)) =
      Completes leaf (value.subst ts) (parameter.subst ts) (count.subst ts) (produced.subst ts) := by
  unfold Completes completionBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph4,graph3,graph2,programSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem completesRename {α β : Type} (leaf : Program 2)
    (value parameter count produced : OTerm α) (j : α → β) :
    (Completes leaf value parameter count produced).relabel j =
      Completes leaf (value.relabel j) (parameter.relabel j) (count.relabel j) (produced.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Completes leaf value parameter count produced).subst (fun a => emb (.var (j a))) = _
  rw [completesSubst]
  simp only [← termRelabelAsSubst]

theorem completionBodyWitness {α : Type} (leaf : Program 2)
    (value parameter count produced work results initial final : OTerm α) :
    (completionBody leaf value parameter count produced).subst
      (Sum.elim Term.var (fun i => emb (![work,results,initial,final] i))) =
    (graph4 OriginalLambdaTraversalInternal.visitState initial value parameter work results ⊓
      graph3 OriginalLambdaTraversalInternal.returnState final produced work results).imp
      (graph2 (OriginalLambdaTraversal.iterate leaf) final count initial) := by
  unfold completionBody
  rw [witnessEmbedding]
  simp only [impSubst,conjunctionSubst,graph4,graph3,graph2,programSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem hasCompletionSubst {α β : Type} (leaf : Program 2)
    (value parameter payload : OTerm α) (ts : α → OTerm β) :
    (HasCompletion leaf value parameter payload).subst (fun a => emb (ts a)) =
      HasCompletion leaf (value.subst ts) (parameter.subst ts) (payload.subst ts) := by
  unfold HasCompletion InternalFiniteBlocks.block OriginalLambdaTraversalInternalCompletion.witnessBody
  rw [exsSubst,bindSubst,liftedEmbedding]
  simp only [conjunctionSubst,completesSubst,weakBoundSubst,payloadFuel,
    InternalApplicationCertifiedResultFoldClosure.payloadFuel,sucSubst,addSubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem hasCompletionRename {α β : Type} (leaf : Program 2)
    (value parameter payload : OTerm α) (j : α → β) :
    (HasCompletion leaf value parameter payload).relabel j =
      HasCompletion leaf (value.relabel j) (parameter.relabel j) (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (HasCompletion leaf value parameter payload).subst (fun a => emb (.var (j a))) = _
  rw [hasCompletionSubst]
  simp only [← termRelabelAsSubst]

theorem witnessBodyWitness {α : Type} (leaf : Program 2)
    (value parameter payload count produced : OTerm α) :
    (OriginalLambdaTraversalInternalCompletion.witnessBody leaf value parameter payload).subst
      (Sum.elim Term.var (fun i => emb (![count,produced] i))) =
    InternalPairingSumBounds.weakBound count (payloadFuel payload) ⊓
      Completes leaf value parameter count produced := by
  unfold OriginalLambdaTraversalInternalCompletion.witnessBody
  rw [witnessEmbedding]
  simp only [conjunctionSubst,completesSubst,weakBoundSubst,payloadFuel,
    InternalApplicationCertifiedResultFoldClosure.payloadFuel,sucSubst,addSubst,
    witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionSyntaxProof
