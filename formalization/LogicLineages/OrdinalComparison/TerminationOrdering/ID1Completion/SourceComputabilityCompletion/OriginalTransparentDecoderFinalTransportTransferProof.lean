module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTargetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalTransparentDecoderValidatorCollapse (GraphEquality)
open OriginalTransparentDecoderFinalTransport
open OriginalContextInsertion OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Transport through independently established graph equality. This helper
has an explicit equivalence parameter; the public exact target does not. -/
theorem weakeningOfGraphEquality (left right : Program 2)
    (he : GraphEquality left right) (ht : PackedWeakening right) :
    PackedWeakening left := by
  intro body alpha Delta d cutoff gamma extended c parameter extendedParameter packed shifted
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph2 shiftPackedRaw shifted cutoff packed ⊓ graph2 left (numeral 1) packed parameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := iffForward (he body alpha (A :: Delta) (numeral 1) packed parameter)
    (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
  obtain ⟨hin⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft h) (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight h))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))
      (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))) ha)))
  obtain ⟨htransport⟩ := ht body alpha (A :: Delta)
    d cutoff gamma extended c parameter extendedParameter packed shifted
  have hout := iffBackward (he body alpha (A :: Delta) (numeral 1) shifted extendedParameter)
    (show Nonempty (Derivation body (A :: Delta) (graph2 right (numeral 1) shifted extendedParameter)) from
      ⟨Derivation.implicationElimination htransport hin⟩)
  obtain ⟨hout⟩ := hout
  exact ⟨Derivation.implicationIntroduction hout⟩

/-- Transport through independently established graph equality. This helper
has an explicit equivalence parameter; the public exact target does not. -/
theorem erasureOfGraphEquality (left right : Program 2)
    (he : GraphEquality left right) (ht : PackedErasure right) :
    PackedErasure left := by
  intro body alpha Delta d cutoff gamma extended c parameter extendedParameter packed erased
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph3 erasePackedRaw erased d cutoff packed ⊓ graph2 left (numeral 1) packed extendedParameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := iffForward (he body alpha (A :: Delta) (numeral 1) packed extendedParameter)
    (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
  obtain ⟨hin⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft h) (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight h))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))
      (OriginalLambdaConstructorGraphSyntaxProof.andIntro (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))) ha)))
  obtain ⟨htransport⟩ := ht body alpha (A :: Delta)
    d cutoff gamma extended c parameter extendedParameter packed erased
  have hout := iffBackward (he body alpha (A :: Delta) (numeral 1) erased parameter)
    (show Nonempty (Derivation body (A :: Delta) (graph2 right (numeral 1) erased parameter)) from
      ⟨Derivation.implicationElimination htransport hin⟩)
  obtain ⟨hout⟩ := hout
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTransferProof
