module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions

/-- Uniform original term-constructor content provenance. Source acceptance,
not a supplied constructor split or child semantic law, supplies every shape
and type constraint. The actual mapped row is in forward child order; it is
NOT asserted equal to the reverse-order runtime result stack. Q is arbitrary,
with no assumed evaluator correctness or fixedpoint equation. -/
def ActualTermReturn : Prop := ∀ (Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
  Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)) →
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) row)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermContentTargets
