module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem prefixAt (R : Program 2) (typ child packed observation typedObservation parameter sourceRaw targetRaw newSourceRaw newTargetRaw source target newSource newTarget certificate frontCode payloadCode newFront newCertificate : OTerm alpha)
 (hSource : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor newSourceRaw typ child sourceRaw)))
 (hTarget : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor newTargetRaw typ child targetRaw)))
 (hPacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (hObservation : Nonempty (Derivation body Delta (graph2 R observation packed parameter)))
 (hTyped : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObservation typ observation)))
 (hSourceTail : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) source sourceRaw parameter)))
 (hTargetTail : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) target targetRaw parameter)))
 (hSourceOut : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) newSource newSourceRaw parameter)))
 (hTargetOut : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) newTarget newTargetRaw parameter)))
 (hEdge : Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) source target certificate)))
 (hCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate frontCode payloadCode)))
 (hFront : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode newFront typedObservation frontCode)))
 (hNewCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newCertificate newFront payloadCode)))
 : Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) newSource newTarget newCertificate)) := by
 have hs := OriginalTypedArgumentObservationsInternalConsProof.forward R newSourceRaw typ child sourceRaw
   packed observation typedObservation source parameter newSource hSource hPacked hObservation hTyped hSourceTail hSourceOut
 have ht := OriginalTypedArgumentObservationsInternalConsProof.forward R newTargetRaw typ child targetRaw
   packed observation typedObservation target parameter newTarget hTarget hPacked hObservation hTyped hTargetTail hTargetOut
 exact OriginalNumericListSortExchangePrependProof.prepend source target certificate frontCode payloadCode
   typedObservation newFront newCertificate newSource newTarget hEdge hCertificate hFront hNewCertificate hs ht
theorem actualPrefix : OriginalTypedArgumentObservationPrefixTargets.ActualPrefix := by
 intro R body alpha Delta typ child packed observation typedObservation parameter sourceRaw targetRaw newSourceRaw newTargetRaw source target newSource newTarget certificate frontCode payloadCode newFront newCertificate hSource hTarget hPacked hObservation hTyped hSourceTail hTargetTail hSourceOut hTargetOut hEdge hCertificate hFront hNewCertificate
 exact prefixAt R typ child packed observation typedObservation parameter sourceRaw targetRaw newSourceRaw newTargetRaw source target newSource newTarget certificate frontCode payloadCode newFront newCertificate hSource hTarget hPacked hObservation hTyped hSourceTail hTargetTail hSourceOut hTargetOut hEdge hCertificate hFront hNewCertificate
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixProof
