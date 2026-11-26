module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every raw spine, including malformed tags, stops within raw+1 steps.
The claim is an actual fixed-point graph at the actual computed output;
no native termination, source validity, or external stopping oracle. -/
def RawTermination : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (count raw acc initial parameter out : OTerm alpha),
 Nonempty (Derivation body Delta (InternalLessThan.strictLess raw count)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial raw acc)) →
 Nonempty (Derivation body Delta (graph3 (walk R) out count initial parameter)) →
 Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationTargets
