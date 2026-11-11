module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObject
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawObjectTransport
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal Object wrapper, inputs [outer context, Object]. The Object is the
original pair (Encodable Gamma, packed payload), and the unchanged validator
receives [payload, pair context Gamma]. No canonical fold or selector is used. -/
def objectValidator (validator : Program 2) : Program 2 :=
  .composition validator
    ![rightOf (.projection 1),pairOf (.projection 0) (leftOf (.projection 1))]

/-- Actual raw Object weakening at cutoff zero. All Object coordinates are
supplied internally, not assumed to be native or canonical. -/
def ObjectWeakening (validator : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d c input shifted : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 shiftObjectRaw shifted d input ⊓
      graph2 (objectValidator validator) (numeral 1) c input).imp
      (graph2 (objectValidator validator) (numeral 1) c shifted)))

/-- Actual raw Object erasure retains the necessary actual context-cons
premise, attached to the SAME input Object. The erased type is unrestricted;
there is no erased-type window, canonicality or transformed bound premise. -/
def ObjectErasure (validator : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d c input erased gamma packed extended : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing input extended packed ⊓
      (graph2 InternalListCodec.consCode extended d gamma ⊓
        (graph1 eraseObjectRaw erased input ⊓
          graph2 (objectValidator validator) (numeral 1) c input))).imp
      (graph2 (objectValidator validator) (numeral 1) c erased)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObject
