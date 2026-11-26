module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Original symbolic numeric list reversal, not a native-list reflection. -/
def ActualLaws : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw count mapped : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count raw)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse mapped raw)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count mapped ⊓
   graph1 OriginalTypedArgumentObservations.reverse raw mapped))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionTargets
