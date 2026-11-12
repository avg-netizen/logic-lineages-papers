module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalTagArithmeticSyntaxProof
open OriginalTypedArgumentObservationsReverseInternalTerminationDefinitions
def ActualTermination : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (raw state acc out : OTerm alpha),
 Nonempty (Derivation body [] ((fields raw state acc out).imp (graph1 InternalUnpair.left z out)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationTargets
