module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationSwapDefinitions OriginalTypedArgumentObservations

/-- Actual original tag7 adjacent swap under an effective common raw prefix.
The existing local certificate keeps its payload; the final front is the actual
mapped packed-cell prefix. No source permutation or native reflection. -/
def ActualAdjacent : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate front mappedFront builtSource builtTarget finalSource finalTarget finalCertificate : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw)))
 (hc : Nonempty (Derivation body Delta (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter)))
 (ho : Nonempty (Derivation body Delta (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter)))
 (hk : Nonempty (Derivation body Delta (Certificate typedQ typedR observedTail rest payload certificate)))
 (hbSource : Nonempty (Derivation body Delta (graph2 OriginalTypedArgumentPrefixBuilder.build builtSource front sourceRaw)))
 (hbTarget : Nonempty (Derivation body Delta (graph2 OriginalTypedArgumentPrefixBuilder.build builtTarget front targetRaw)))
 (hm : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentPrefixBuilder.mapped R) mappedFront front parameter)))
 (hSource : Nonempty (Derivation body Delta (graph2 (argumentObservations R) finalSource builtSource parameter)))
 (hTarget : Nonempty (Derivation body Delta (graph2 (argumentObservations R) finalTarget builtTarget parameter)))
 (hCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing finalCertificate mappedFront payload))),
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) finalSource finalTarget finalCertificate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentTargets
