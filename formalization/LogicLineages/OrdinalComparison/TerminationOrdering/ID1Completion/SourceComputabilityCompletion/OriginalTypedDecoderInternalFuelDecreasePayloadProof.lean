module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelChildBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalPairingSumBounds
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalBinarySyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalFuelChildBoundsProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem applicationPayloadBound (raw payload domain first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 2) payload)))
    (hc : Nonempty (Derivation body Delta (StepBinaryPayload payload domain first second))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  apply stepBinaryPayloadCases payload domain first second _ hc
  intro beta j Theta children hj hm hs
  simp only [weakBound,InternalLessThan.strictLess,childFuelSum,orderRename,addRelabel,sucRelabel]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  exact applicationBound (raw.relabel j) (payload.relabel j) children (domain.relabel j)
    (first.relabel j) (second.relabel j) hp' hm hs

 theorem consPayloadBound (raw payload domain first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
    (hc : Nonempty (Derivation body Delta (StepBinaryPayload payload domain first second))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  apply stepBinaryPayloadCases payload domain first second _ hc
  intro beta j Theta children hj hm hs
  simp only [weakBound,InternalLessThan.strictLess,childFuelSum,orderRename,addRelabel,sucRelabel]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  exact consBound (raw.relabel j) (payload.relabel j) children (domain.relabel j)
    (first.relabel j) (second.relabel j) hp' hm hs

 theorem numberedPayloadBound (raw payload label head typ base types extras : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (hc : Nonempty (Derivation body Delta
      (StepNumberedPayload payload label head typ base types extras))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum base extras) raw)) := by
  apply stepNumberedPayloadCases payload label head typ base types extras _ hc
  intro beta j Theta ys hj fields
  simp only [weakBound,InternalLessThan.strictLess,childFuelSum,orderRename,addRelabel,sucRelabel]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  exact numberedBound (raw.relabel j) (payload.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    (label.relabel j) (head.relabel j) (typ.relabel j) (base.relabel j)
    (types.relabel j) (extras.relabel j) hp' (andLeft fields) (andLeft (andRight fields))
    (andLeft (andRight (andRight fields))) (andLeft (andRight (andRight (andRight fields))))
    (andRight (andRight (andRight (andRight fields))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePayloadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePayloadProof
