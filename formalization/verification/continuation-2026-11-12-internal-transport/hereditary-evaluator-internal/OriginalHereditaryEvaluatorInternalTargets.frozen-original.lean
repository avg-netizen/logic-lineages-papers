module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructors
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Operational projection only: the actual run witness is explicit. -/
def RunProjection : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (packed parameter count initial final work results value : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.computedFuel count packed parameter)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.initial initial packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) final count initial)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing final work results)) →
 Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode value results)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter))
/-- Empty actual work is a fixed point for any internally quantified count. -/
def EmptyWorkIteration : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (state results count : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z results)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) state count state))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalTargets
