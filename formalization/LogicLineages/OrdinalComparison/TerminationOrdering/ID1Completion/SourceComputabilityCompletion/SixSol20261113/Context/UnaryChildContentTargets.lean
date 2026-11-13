module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryChildContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions

/-- The literal lambda child scan supplies its scalar observation at the actual
extended parameter. No child computation or parameter-extension graph is a
premise: the original expansion must produce that parameter internally.
This is local proof-side content provenance, not evaluator correctness. -/
def LambdaReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw domain child codomain parameter jobs annotatedPrefix row first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ domain codomain)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 1) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first z)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

/-- The original ordinary-symbol child is an argument-list job, not a term
job. Its mapped singleton supplies the list observation consumed by returnRoot
at the unchanged original parameter, without a supplied child semantic law. -/
def OrdinaryReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw head base parameter jobs annotatedPrefix row first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 1) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first z)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryChildContentTargets
