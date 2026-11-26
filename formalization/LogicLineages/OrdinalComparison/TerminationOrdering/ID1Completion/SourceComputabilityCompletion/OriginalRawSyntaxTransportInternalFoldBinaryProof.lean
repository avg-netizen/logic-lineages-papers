module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionInductionProof OriginalRawSyntaxTransportInternalMachineCompletionBinaryProof
open OriginalRawSyntaxTransportInternalMachineCompletionRunProof OriginalRawSyntaxTransportInternalMachineCompletionOutputProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open OriginalLambdaTraversalInternalPayloadArithmeticProof (applicationCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCompletions (mode : Mode) (d k raw first second firstOut secondOut out cf ca : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hcfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel first))))
    (hcab : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound ca (payloadFuel second))))
    (hcfc : Nonempty (Derivation positive Delta (Completes mode d k first cf firstOut)))
    (hcac : Nonempty (Derivation positive Delta (Completes mode d k second ca secondOut)))
    (hr : Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw firstOut secondOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  completionFold mode d k raw (suc (add cf (add ca (suc z)))) out
    (applicationCount raw first second cf ca
      (binaryChildBound raw first second (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))) hcfb hcab)
    (binaryComplete mode d k raw first second cf ca firstOut secondOut out hf hr hcfc hcac)

theorem atFirstCompletion (mode : Mode) (d k raw first second firstOut secondOut out cf : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hcfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel first))))
    (hcfc : Nonempty (Derivation positive Delta (Completes mode d k first cf firstOut)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) secondOut d k second)))
    (hr : Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw firstOut secondOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) := by
  apply completionAtFoldCases mode d k second secondOut _ hsecond (hasCompletion mode d k second)
  intro beta j Theta ca hj hcab hcac
  rw [graph3Rename]
  have hf' := renameInto hf j Theta hj
  have hcfb' := renameInto hcfb j Theta hj
  have hcfc' := renameInto hcfc j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [binaryFieldsRename] at hf'
  simp only [weakBoundRename,payloadFuelRename] at hcfb'
  rw [completesRename] at hcfc'
  rw [graph3Rename] at hr'
  exact atCompletions mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    (firstOut.relabel j) (secondOut.relabel j) (out.relabel j) (cf.relabel j) ca hf' hcfb' hcab hcfc' hcac hr'

theorem binaryBackward (mode : Mode) (d k raw first second firstOut secondOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) firstOut d k first)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) secondOut d k second)))
    (hr : Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw firstOut secondOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) := by
  apply completionAtFoldCases mode d k first firstOut _ hfirst (hasCompletion mode d k first)
  intro beta j Theta cf hj hcfb hcfc
  rw [graph3Rename]
  have hf' := renameInto hf j Theta hj
  have hsecond' := renameInto hsecond j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [binaryFieldsRename] at hf'
  rw [graph3Rename] at hsecond' hr'
  exact atFirstCompletion mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    (firstOut.relabel j) (secondOut.relabel j) (out.relabel j) cf hf' hcfb hcfc hsecond' hr'

theorem binaryForward (mode : Mode) (d k raw first second firstOut secondOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) firstOut d k first)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) secondOut d k second)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw firstOut secondOut)) := by
  apply programCases (rebuild mode) (Fin.cons raw (Fin.cons firstOut (Fin.cons secondOut Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hp
  have hf' := renameInto hf j Theta hj
  have hfirst' := renameInto hfirst j Theta hj
  have hsecond' := renameInto hsecond j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [binaryFieldsRename] at hf'
  rw [graph3Rename] at hfirst' hsecond' ho'
  have hfold := binaryBackward mode (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    (firstOut.relabel j) (secondOut.relabel j) produced hf' hfirst' hsecond' hp
  exact outputTransport (rebuild mode) produced (out.relabel j)
    ![raw.relabel j,firstOut.relabel j,secondOut.relabel j]
    (valueUnique (fold mode) produced (out.relabel j) ![d.relabel j,k.relabel j,raw.relabel j] hfold ho') hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
