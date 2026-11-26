module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine internal original-source descent. The actual context witnesses
are supplied by the caller; all hidden raw lambda coordinates are recovered
internally. No native calibration, child validity, or whole-step oracle. -/
def ActualSourceLambdaChild : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (H G : Program 1) (M W : Program 2)
   (s parameter child d e arrow c gamma extended childParam : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e child arrow)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one s parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one child childParam))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildTargets
