module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual source root, actual literal initial encoded state and computed fuel.
No Job/Agenda, potential bound, native typing, or completion is a premise.
Only empty final work is concluded; result semantics are separate. -/
def ActualSourceRootCompletion : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching B job)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel job)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)) →
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionTargets
