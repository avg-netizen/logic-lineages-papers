module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace
/-- Successful front exposes one actual guarded old hop and same tail run. No source-transport, erasure or rank result enters this premise. State queries remain literal; a later wrapper unpacks their coordinates. -/
def ActualFrontDescent : Prop := ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (code head tail state next out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
 Nonempty (Derivation body Delta (graph1 (transition source leaf) next state)) →
 Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out code state)) →
 Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out)) →
 Nonempty (Derivation body Delta
  (((graph1 (OriginalHereditaryLambda.atState (lambdaHop source leaf)) (suc z) state ⊓
     graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state) ⊔
    (graph1 (OriginalHereditaryLambda.atState (applicationHop source leaf)) (suc z) state ⊓
     graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state)) ⊓
   InternalRawListRepeat.repeatGraph (transition source leaf) out tail next))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentTargets
