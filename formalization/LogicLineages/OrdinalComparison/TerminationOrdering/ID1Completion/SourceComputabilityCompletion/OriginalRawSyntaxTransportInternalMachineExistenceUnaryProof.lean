module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionBindingProof
open OriginalRawSyntaxTransportInternalMachineCompletionUnaryProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open OriginalLambdaTraversalInternalPayloadArithmeticProof (lambdaCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromRun (mode : Mode) (d k raw child childK count childOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc child) raw)))
    (hcb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel child))))
    (hcc : Nonempty (Derivation positive Delta (Completes mode d childK child count childOut))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply programCases (rebuild mode) (Fin.cons raw (Fin.cons childOut (Fin.cons z Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hcb' := renameInto hcb j Theta hj
  have hcc' := renameInto hcc j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [weakBoundRename,sucRelabel] at hb'
  simp only [weakBoundRename,payloadFuelRename] at hcb'
  rw [completesRename] at hcc'
  simp only [consTermRename,emptyRename,zRelabel] at hp
  exact hasCompletionIntro mode (d.relabel j) (k.relabel j) (raw.relabel j) (raw.relabel j)
    (suc (suc (count.relabel j))) produced
    (lambdaCount (raw.relabel j) (child.relabel j) (count.relabel j) hb' hcb')
    (unaryComplete mode (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
      (childK.relabel j) (count.relabel j) (childOut.relabel j) produced hf' hp hcc')

theorem fromChild (mode : Mode) (d k raw child childK : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc child) raw)))
    (hc : Nonempty (Derivation positive Delta (HasCompletion mode d childK child child))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply hasCompletionCases mode d childK child child _ hc
  intro beta j Theta count childOut hj hcb hcc
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [weakBoundRename,sucRelabel] at hb'
  exact fromRun mode (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
    (childK.relabel j) count childOut hf' hb' hcb hcc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceUnaryProof
