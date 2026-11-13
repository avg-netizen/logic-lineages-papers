module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original computed-fuel query, with all final shape witnesses constructed. -/
def ActualSourceRootShape : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
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
 Nonempty (Derivation body Delta (RootResultDefinitions.Shape R packed parameter output))

/-- Original computed-fuel query; literal root projection replaces supplied final geometry. -/
def ActualSourceRootReadback : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output root : OTerm alpha),
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
 Nonempty (Derivation body Delta (graph1 RootResultDefinitions.rootOfState root output)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter))

/-- Genuine final return producer; its continuation is discharged in the shape/readback endpoints. -/
def ActualSourceRootReturnCases : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output : OTerm alpha) (psi : Formula alpha),
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
 RootResultDefinitions.ReturnConsumer R body Delta packed parameter output psi →
 Nonempty (Derivation body Delta psi)

/-- Readback through the ACTUAL unchanged computed-fuel evaluator; no explicit
job/fuel/state geometry, final cons witness or result invariant is a premise. -/
def ActualEvaluatorReadback : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (H G : Program 1) (M W : Program 2) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter value root : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left root value)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultTargets
