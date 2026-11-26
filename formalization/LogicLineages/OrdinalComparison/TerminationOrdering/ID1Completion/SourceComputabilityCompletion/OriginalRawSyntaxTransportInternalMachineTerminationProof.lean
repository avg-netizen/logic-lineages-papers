module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineTerminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionBindingProof OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
open OriginalRawSyntaxTransportInternalMachineRunStateProof OriginalRawSyntaxTransportInternalMachineIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open OriginalLambdaTraversalInternal (FinishedRun)
open InternalDerivationRenamingSyntaxProof (existsRename)
open OriginalLambdaTraversalInternalRunStateProof (finishedCases finishedAsReturn finishedRunIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem finishedRunRename {beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    (FinishedRun state).relabel j = FinishedRun (state.relabel j) := by
  simp only [FinishedRun,existsRename,graph1Rename,Term.relabel,Term.relabel_relabel] <;> rfl

theorem iterateAtStates (mode : Mode) (d k raw count budget produced start finish : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hbudget : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budget)))
    (hc : Nonempty (Derivation positive Delta (Completes mode d k raw count produced)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hf : Nonempty (Derivation positive Delta (graph1 finishedState finish produced))) :
    Nonempty (Derivation positive Delta (graph2 (iterate mode) finish budget start)) := by
  apply finishedCases finish produced _ hf
  intro beta j Theta singleton hj hs he
  rw [graph2Rename]
  have hb' := renameInto hb j Theta hj
  have hbudget' := renameInto hbudget j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at hf'
  rw [graph3Rename] at hi'
  simp only [weakBoundRename,payloadFuelRename] at hb' hbudget'
  rw [completesRename] at hc'
  have ht := completesApply mode (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j)
    (produced.relabel j) z z (start.relabel j) (finish.relabel j) hc'
    (initialAsVisit (start.relabel j) (d.relabel j) (k.relabel j) (raw.relabel j) hi')
    (finishedAsReturn (finish.relabel j) (produced.relabel j) hf')
  exact iteratePadding mode (count.relabel j) (budget.relabel j) (start.relabel j) (finish.relabel j) singleton
    (weakTrans (count.relabel j) (payloadFuel (raw.relabel j)) (budget.relabel j) hb' hbudget') he ht

theorem terminalFromCompletion (mode : Mode) (d k raw count budget produced start state : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hbudget : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budget)))
    (hc : Nonempty (Derivation positive Delta (Completes mode d k raw count produced)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate mode) state budget start))) :
    Nonempty (Derivation positive Delta (FinishedRun state)) := by
  apply programCases finishedState (Fin.cons produced Fin.elim0) _
  intro beta j Theta finish hj hf
  rw [finishedRunRename]
  have hb' := renameInto hb j Theta hj
  have hbudget' := renameInto hbudget j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [weakBoundRename,payloadFuelRename] at hb' hbudget'
  rw [completesRename] at hc'
  rw [graph3Rename] at hi'
  rw [graph2Rename] at hr'
  simp only [consTermRename,emptyRename] at hf
  have hfinish := iterateAtStates mode (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j)
    (budget.relabel j) (produced.relabel j) (start.relabel j) finish hb' hbudget' hc' hi' hf
  have he := valueUnique (iterate mode) finish (state.relabel j) ![budget.relabel j,start.relabel j] hfinish hr'
  have hstate := outputTransport finishedState finish (state.relabel j) ![produced.relabel j] he hf
  exact finishedRunIntro (state.relabel j) (produced.relabel j) hstate

/-- Every run at a budget at least the literal 2*raw+1 reaches an original
live state with empty work and exactly one result. All witnesses and the
sufficient-fuel argument are constructed inside the original arithmetic. -/
theorem sufficientTerminal (mode : Mode) (d k raw budget start state : OTerm alpha)
    (hbudget : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budget)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hr : Nonempty (Derivation positive Delta (graph2 (iterate mode) state budget start))) :
    Nonempty (Derivation positive Delta (FinishedRun state)) := by
  apply hasCompletionCases mode d k raw raw _ (hasCompletion mode d k raw)
  intro beta j Theta count produced hj hb hc
  rw [finishedRunRename]
  have hbudget' := renameInto hbudget j Theta hj
  have hi' := renameInto hi j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [weakBoundRename,payloadFuelRename] at hbudget'
  rw [graph3Rename] at hi'
  rw [graph2Rename] at hr'
  exact terminalFromCompletion mode (d.relabel j) (k.relabel j) (raw.relabel j) count
      (budget.relabel j) produced (start.relabel j) (state.relabel j) hb hbudget' hc hi' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineTerminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineTerminationProof
