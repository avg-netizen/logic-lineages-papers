module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ZeroPrefix : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (typedQ typedR observedTail observedY observedX source target rest payload certificate : OTerm alpha)
 (hRest : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rest typedR observedTail)))
 (hPayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload typedQ rest)))
 (hCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate z payload)))
 (cY : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode observedY typedR observedTail)))
 (cX : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode observedX typedQ observedTail)))
 (cXY : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode source typedQ observedY)))
 (cYX : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode target typedR observedX))),
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) source target certificate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionTargets
