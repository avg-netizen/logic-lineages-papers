module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One actual original typed cons extends a common prefix of an accepted
observed adjacent exchange. The child and parameter are identical; original
and extended certificates share their exact payload. No source Perm oracle. -/
def ActualPrefix : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (typ child packed observation typedObservation parameter sourceRaw targetRaw newSourceRaw newTargetRaw source target newSource newTarget certificate frontCode payloadCode newFront newCertificate : OTerm alpha)
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
 (hNewCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newCertificate newFront payloadCode))),
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) newSource newTarget newCertificate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationPrefixTargets
