module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original actual source root and computed fuel, now requiring the actual final
result root coordinate to be its original root observation. No return-frame,
result-stack invariant, native correctness, or source-root completion premise.
Child/deletion return content and observer fixed-point remain separate. -/
def ActualSourceRootProjection : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output outWork stack value old root tail : OTerm alpha),
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
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionTargets
