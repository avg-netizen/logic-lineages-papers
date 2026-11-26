module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionBindingProof
open OriginalRawSyntaxTransportInternalMachineCompletionBinaryProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open InternalPairingSumBounds (childFuelSum)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalLambdaTraversalInternalPayloadArithmeticProof (applicationCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromRuns (mode : Mode) (d k raw first second cf ca firstOut secondOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (childFuelSum first second) raw)))
    (hcfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel first))))
    (hcab : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound ca (payloadFuel second))))
    (hcfc : Nonempty (Derivation positive Delta (Completes mode d k first cf firstOut)))
    (hcac : Nonempty (Derivation positive Delta (Completes mode d k second ca secondOut))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply programCases (rebuild mode) (Fin.cons raw (Fin.cons firstOut (Fin.cons secondOut Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hcfb' := renameInto hcfb j Theta hj
  have hcab' := renameInto hcab j Theta hj
  have hcfc' := renameInto hcfc j Theta hj
  have hcac' := renameInto hcac j Theta hj
  rw [binaryFieldsRename] at hf'
  simp only [weakBoundRename,childFuelSum,sucRelabel,addRelabel] at hb'
  simp only [weakBoundRename,payloadFuelRename] at hcfb' hcab'
  rw [completesRename] at hcfc' hcac'
  simp only [consTermRename,emptyRename] at hp
  exact hasCompletionIntro mode (d.relabel j) (k.relabel j) (raw.relabel j) (raw.relabel j)
    (suc (add (cf.relabel j) (add (ca.relabel j) (suc z)))) produced
    (applicationCount (raw.relabel j) (first.relabel j) (second.relabel j)
      (cf.relabel j) (ca.relabel j) hb' hcfb' hcab')
    (binaryComplete mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
      (cf.relabel j) (ca.relabel j) (firstOut.relabel j) (secondOut.relabel j) produced hf' hp hcfc' hcac')

theorem fromFirstRun (mode : Mode) (d k raw first second cf firstOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (childFuelSum first second) raw)))
    (hcfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel first))))
    (hcfc : Nonempty (Derivation positive Delta (Completes mode d k first cf firstOut)))
    (hca : Nonempty (Derivation positive Delta (HasCompletion mode d k second second))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply hasCompletionCases mode d k second second _ hca
  intro beta j Theta ca secondOut hj hcab hcac
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hcfb' := renameInto hcfb j Theta hj
  have hcfc' := renameInto hcfc j Theta hj
  rw [binaryFieldsRename] at hf'
  simp only [weakBoundRename,childFuelSum,sucRelabel,addRelabel] at hb'
  simp only [weakBoundRename,payloadFuelRename] at hcfb'
  rw [completesRename] at hcfc'
  exact fromRuns mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    (cf.relabel j) ca (firstOut.relabel j) secondOut hf' hb' hcfb' hcab hcfc' hcac

theorem fromChildren (mode : Mode) (d k raw first second : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (childFuelSum first second) raw)))
    (hcf : Nonempty (Derivation positive Delta (HasCompletion mode d k first first)))
    (hca : Nonempty (Derivation positive Delta (HasCompletion mode d k second second))) :
    Nonempty (Derivation positive Delta (HasCompletion mode d k raw raw)) := by
  apply hasCompletionCases mode d k first first _ hcf
  intro beta j Theta cf firstOut hj hcfb hcfc
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hca' := renameInto hca j Theta hj
  rw [binaryFieldsRename] at hf'
  simp only [weakBoundRename,childFuelSum,sucRelabel,addRelabel] at hb'
  rw [hasCompletionRename] at hca'
  exact fromFirstRun mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    cf firstOut hf' hb' hcfb hcfc hca'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExistenceBinaryProof
