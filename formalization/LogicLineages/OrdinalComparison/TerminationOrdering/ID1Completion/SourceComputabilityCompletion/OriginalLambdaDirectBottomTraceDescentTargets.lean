module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
/-- Successful original front cell exposes a genuine guarded old hop and the
actual child-live state, with the same terminal output and unchanged tail run.
The transition graph is an actual total query, not a correctness premise.
No transformed edge, rank or source-transport conclusion is assumed. -/
def ActualFrontDescent : Prop := ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter code head tail state next out : OTerm alpha),
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path code s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
 Nonempty (Derivation body Delta (graph1 (transition source leaf) next state)) →
 Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out code state)) →
 Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out)) →
 Nonempty (Derivation body Delta
  (graph4 (hop source leaf) (suc z) s t cert parameter ⊓
   (graph4 OriginalHereditaryLambda.childLive next s t cert parameter ⊓
    InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentTargets
