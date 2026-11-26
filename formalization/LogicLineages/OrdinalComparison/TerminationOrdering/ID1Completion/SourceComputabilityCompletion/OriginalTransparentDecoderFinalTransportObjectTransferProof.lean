module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalTransparentDecoderFinalTransport OriginalTransparentDecoderFinalTransportObject
open OriginalTransparentDecoderFinalTransportObjectCoordinatesProof
open OriginalRawObjectTransport OriginalRawObjectTransportInternalExposureProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every actual Object shift is exposed internally and transported through
the SAME validator. This needs only its independently established packed law. -/
theorem objectWeakeningOfPacked (validator : Program 2) (ht : PackedWeakening validator) :
    ObjectWeakening validator := by
  intro body alpha Delta d c input shifted
  let A := graph2 shiftObjectRaw shifted d input ⊓
    graph2 (objectValidator validator) (numeral 1) c input
  let B := graph2 (objectValidator validator) (numeral 1) c shifted
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have moved : Nonempty (Derivation body (A :: Delta) B) := by
    apply actualRawObjectInternalShiftExposure body alpha (A :: Delta) d input shifted B
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft h)
    intro beta j Theta hj gamma packed extended transformed hh
    simp only [B,graph2Rename,numeralRename]
    have ha := renameInto (OriginalLambdaConstructorGraphSyntaxProof.andRight h) j Theta hj
    simp only [graph2Rename,numeralRename] at ha
    exact objectWeakeningAt validator ht (d.relabel j) (c.relabel j) (input.relabel j)
      (shifted.relabel j) gamma packed extended transformed
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft hh) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))) (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))) ha
  obtain ⟨moved⟩ := moved
  exact ⟨Derivation.implicationIntroduction moved⟩

/-- The erase wrapper's original cons premise is retained through exposure.
No nonempty-context, erased-type-window or canonical premise is invented. -/
theorem objectErasureOfPacked (validator : Program 2) (ht : PackedErasure validator) :
    ObjectErasure validator := by
  intro body alpha Delta d c input erased gamma packed extended
  let A := graph2 InternalPairing.pairing input extended packed ⊓
    (graph2 InternalListCodec.consCode extended d gamma ⊓
      (graph1 eraseObjectRaw erased input ⊓
        graph2 (objectValidator validator) (numeral 1) c input))
  let B := graph2 (objectValidator validator) (numeral 1) c erased
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have moved : Nonempty (Derivation body (A :: Delta) B) := by
    apply actualRawObjectInternalEraseExposure body alpha (A :: Delta)
      d input erased gamma packed extended B (OriginalLambdaConstructorGraphSyntaxProof.andLeft h) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight h))
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))
    intro beta j Theta hj transformed hh
    simp only [B,graph2Rename,numeralRename]
    have ha := renameInto (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))) j Theta hj
    simp only [graph2Rename,numeralRename] at ha
    exact objectErasureAt validator ht (d.relabel j) (c.relabel j) (input.relabel j)
      (erased.relabel j) (gamma.relabel j) (packed.relabel j) (extended.relabel j) transformed
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft hh) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))
      (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))) (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight hh))) ha
  obtain ⟨moved⟩ := moved
  exact ⟨Derivation.implicationIntroduction moved⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectTransferProof
