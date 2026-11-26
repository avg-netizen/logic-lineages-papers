module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExistenceUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
open OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open OriginalLambdaTraversalInternalPayloadArithmeticProof (lambdaCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromRun (d k raw child childK count childOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc child) raw)))
    (hcb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel child))))
    (hcc : Nonempty (Derivation positive Delta (Completes d childK child count childOut))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply programCases (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) (Fin.cons raw (Fin.cons childOut (Fin.cons z Fin.elim0))) _
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
  exact hasCompletionIntro (d.relabel j) (k.relabel j) (raw.relabel j) (raw.relabel j)
    (suc (suc (count.relabel j))) produced
    (lambdaCount (raw.relabel j) (child.relabel j) (count.relabel j) hb' hcb')
    (unaryComplete (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
      (childK.relabel j) (count.relabel j) (childOut.relabel j) produced hf' hp hcc')

theorem fromChild (d k raw child childK : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc child) raw)))
    (hc : Nonempty (Derivation positive Delta (HasCompletion d childK child child))) :
    Nonempty (Derivation positive Delta (HasCompletion d k raw raw)) := by
  apply hasCompletionCases d childK child child _ hc
  intro beta j Theta count childOut hj hcb hcc
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [weakBoundRename,sucRelabel] at hb'
  exact fromRun (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
    (childK.relabel j) count childOut hf' hb' hcb hcc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExistenceUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExistenceUnaryProof
