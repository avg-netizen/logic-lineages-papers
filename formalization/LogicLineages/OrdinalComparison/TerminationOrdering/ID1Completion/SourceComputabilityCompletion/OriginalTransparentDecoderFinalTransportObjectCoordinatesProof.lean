module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalTransparentDecoderFinalTransportObject
open OriginalTransparentDecoderFinalTransportObjectFieldsProof
open OriginalTransparentDecoderFinalTransport OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open InternalParameterizedNumericIterationSyntaxProof (pairValuesCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Zero-cutoff packed weakening at known actual Object coordinates.
Both parameter pairs are supplied internally by original pair totality. -/
theorem objectWeakeningAt (validator : Program 2) (ht : PackedWeakening validator)
    (d c input shifted gamma packed extended transformed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extended d gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 shiftPackedRaw transformed (numeral 0) packed)))
    (ho : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing shifted extended transformed)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (objectValidator validator) (numeral 1) c input))) :
    Nonempty (Derivation body Delta
      (graph2 (objectValidator validator) (numeral 1) c shifted)) := by
  apply pairValuesCases c (![gamma,extended] : Fin 2 → OTerm alpha) _
  intro beta j Theta parameters hj hparameters
  simp only [graph2Rename,numeralRename]
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename] at hp'
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename] at hc'
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,numeralRename] at hr'
  have ho' := renameInto ho j Theta hj
  simp only [graph2Rename] at ho'
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    (d.relabel j) (gamma.relabel j) (extended.relabel j) hc'
  have accepted := objectFieldsElim validator (numeral 1) (c.relabel j) (input.relabel j)
    (gamma.relabel j) (packed.relabel j) (parameters 0) hp' (hparameters 0) ha'
  have moved := implicationApply
    (ht body beta Theta (d.relabel j) (numeral 0) (gamma.relabel j) (extended.relabel j)
      (c.relabel j) (parameters 0) (parameters 1) (packed.relabel j) (transformed.relabel j))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro hi
      (OriginalLambdaConstructorGraphSyntaxProof.andIntro (hparameters 0)
        (OriginalLambdaConstructorGraphSyntaxProof.andIntro (hparameters 1)
          (OriginalLambdaConstructorGraphSyntaxProof.andIntro hr' accepted))))
  exact objectFieldsIntro validator (numeral 1) (c.relabel j) (shifted.relabel j)
    (extended.relabel j) (transformed.relabel j) (parameters 1) ho' (hparameters 1) moved

/-- Zero-cutoff packed erasure at known actual Object coordinates.
Both parameter pairs are supplied internally by original pair totality. -/
theorem objectErasureAt (validator : Program 2) (ht : PackedErasure validator)
    (d c input erased gamma packed extended transformed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input extended packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extended d gamma)))
    (hr : Nonempty (Derivation body Delta (graph3 erasePackedRaw transformed d (numeral 0) packed)))
    (ho : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing erased gamma transformed)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (objectValidator validator) (numeral 1) c input))) :
    Nonempty (Derivation body Delta
      (graph2 (objectValidator validator) (numeral 1) c erased)) := by
  apply pairValuesCases c (![gamma,extended] : Fin 2 → OTerm alpha) _
  intro beta j Theta parameters hj hparameters
  simp only [graph2Rename,numeralRename]
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename] at hp'
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename] at hc'
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,numeralRename] at hr'
  have ho' := renameInto ho j Theta hj
  simp only [graph2Rename] at ho'
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    (d.relabel j) (gamma.relabel j) (extended.relabel j) hc'
  have accepted := objectFieldsElim validator (numeral 1) (c.relabel j) (input.relabel j)
    (extended.relabel j) (packed.relabel j) (parameters 1) hp' (hparameters 1) ha'
  have moved := implicationApply
    (ht body beta Theta (d.relabel j) (numeral 0) (gamma.relabel j) (extended.relabel j)
      (c.relabel j) (parameters 0) (parameters 1) (packed.relabel j) (transformed.relabel j))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro hi
      (OriginalLambdaConstructorGraphSyntaxProof.andIntro (hparameters 0)
        (OriginalLambdaConstructorGraphSyntaxProof.andIntro (hparameters 1)
          (OriginalLambdaConstructorGraphSyntaxProof.andIntro hr' accepted))))
  exact objectFieldsIntro validator (numeral 1) (c.relabel j) (erased.relabel j)
    (gamma.relabel j) (transformed.relabel j) (parameters 0) ho' (hparameters 0) moved

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectCoordinatesProof
