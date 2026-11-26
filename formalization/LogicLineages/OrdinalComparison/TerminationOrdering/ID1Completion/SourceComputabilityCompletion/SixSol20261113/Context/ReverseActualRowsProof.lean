module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseActualRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem singleton (forwardRow backwardRow first : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode forwardRow first z)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow first z)) :=
  OriginalTypedArgumentObservationsReverseInternalProof.forward z first forwardRow forwardRow z backwardRow
    hc (InternalApplicationValidityStackAppendListProof.appendZeroValue forwardRow) OriginalReverseConsProof.zero hr

theorem binaryAtSingleton (forwardRow backwardRow first second tail singletonFirst : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode forwardRow first tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singletonFirst first z)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow second singletonFirst)) := by
  have ha := InternalApplicationValidityStackAppendListProof.consBackward singletonFirst first z tail tail forwardRow
    hf (InternalApplicationValidityStackAppendListProof.appendZeroValue tail) hc
  have hrev := OriginalReverseConsProof.actualCons body alpha Delta singletonFirst first z singletonFirst z singletonFirst
    hf hf OriginalReverseConsProof.zero (InternalApplicationValidityStackAppendListProof.appendZeroValue singletonFirst)
  exact OriginalTypedArgumentObservationsReverseInternalProof.forward singletonFirst second tail forwardRow singletonFirst backwardRow ht ha hrev hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseActualRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseActualRowsProof
