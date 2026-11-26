module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
def ActualCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw head tail singleton mapped out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton head z)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse mapped tail)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mapped singleton)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out raw))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsTargets
