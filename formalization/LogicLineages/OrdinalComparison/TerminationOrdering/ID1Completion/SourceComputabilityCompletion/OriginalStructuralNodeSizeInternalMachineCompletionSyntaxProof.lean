module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationStepPeel (graph5)
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

open OriginalStructuralNodeSizeInternalMachineCompletion

theorem completesSubst {α β : Type}
    (d k value count produced : OTerm α) (ts : α → OTerm β) :
    (Completes d k value count produced).subst (fun a => emb (ts a)) =
      Completes (d.subst ts) (k.subst ts) (value.subst ts) (count.subst ts) (produced.subst ts) := by
  unfold Completes completionBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph5,graph3,graph2,programSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem completesRename {α β : Type}
    (d k value count produced : OTerm α) (j : α → β) :
    (Completes d k value count produced).relabel j =
      Completes (d.relabel j) (k.relabel j) (value.relabel j) (count.relabel j) (produced.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Completes d k value count produced).subst (fun a => emb (.var (j a))) = _
  rw [completesSubst]
  simp only [← termRelabelAsSubst]

theorem completionBodyWitness {α : Type}
    (d k value count produced work results initial final : OTerm α) :
    (completionBody d k value count produced).subst
      (Sum.elim Term.var (fun i => emb (![work,results,initial,final] i))) =
    (graph5 OriginalRawSyntaxTransportInternalMachineState.visitState initial d k value work results ⊓
      graph3 OriginalRawSyntaxTransportInternalMachineState.returnState final produced work results).imp
      (graph2 (OriginalStructuralNodeSize.iterate) final count initial) := by
  unfold completionBody
  rw [witnessEmbedding]
  simp only [impSubst,conjunctionSubst,graph5,graph3,graph2,programSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem hasCompletionSubst {α β : Type}
    (d k value payload : OTerm α) (ts : α → OTerm β) :
    (HasCompletion d k value payload).subst (fun a => emb (ts a)) =
      HasCompletion (d.subst ts) (k.subst ts) (value.subst ts) (payload.subst ts) := by
  unfold HasCompletion InternalFiniteBlocks.block OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody
  rw [exsSubst,bindSubst,liftedEmbedding]
  simp only [conjunctionSubst,completesSubst,weakBoundSubst,payloadFuel,
    InternalApplicationCertifiedResultFoldClosure.payloadFuel,sucSubst,addSubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem hasCompletionRename {α β : Type}
    (d k value payload : OTerm α) (j : α → β) :
    (HasCompletion d k value payload).relabel j =
      HasCompletion (d.relabel j) (k.relabel j) (value.relabel j) (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (HasCompletion d k value payload).subst (fun a => emb (.var (j a))) = _
  rw [hasCompletionSubst]
  simp only [← termRelabelAsSubst]

theorem witnessBodyWitness {α : Type}
    (d k value payload count produced : OTerm α) :
    (OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody d k value payload).subst
      (Sum.elim Term.var (fun i => emb (![count,produced] i))) =
    InternalPairingSumBounds.weakBound count (payloadFuel payload) ⊓
      Completes d k value count produced := by
  unfold OriginalStructuralNodeSizeInternalMachineCompletion.witnessBody
  rw [witnessEmbedding]
  simp only [conjunctionSubst,completesSubst,weakBoundSubst,payloadFuel,
    InternalApplicationCertifiedResultFoldClosure.payloadFuel,sucSubst,addSubst,
    witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
