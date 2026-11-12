module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions (accumulated)
/-- Arbitrary original numeric list, no native decoding. Appending a fixed suffix
to the initial accumulator appends it to the final accumulator. -/
def ActualCompatibility : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw acc1 acc2 suffix left right : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)) →
 Nonempty (Derivation body Delta (graph2 accumulated left raw acc1)) →
 Nonempty (Derivation body Delta (graph2 accumulated right raw acc2)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append right left suffix))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityTargets
