module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedChildContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions

/-- The original numbered symbol schedules its base arguments before its extra
arguments. Both are list-role jobs at the unchanged original parameter. Their
actual mapped two-child scan supplies returnRoot, with every original numeric
label, head, encoded type and extra-type field retained. No child observation
is supplied as a semantic premise, and no runtime output equality is claimed. -/
def NumberedReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw label head encodedType base extraTypes extras parameter jobs annotatedPrefix row first resultTail second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
    (Fin.cons label (Fin.cons head (Fin.cons encodedType (Fin.cons base (Fin.cons extraTypes (Fin.cons extras Fin.elim0)))))))) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 2) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first resultTail)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode resultTail second z)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedChildContentTargets
