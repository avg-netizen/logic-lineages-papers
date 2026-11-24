module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeMeasureProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalMeasuredThinEdgeMeasureProof (exact_OpenThinMeasuredEdgePreservesMeasure)

/-- Symbolic conservation of the *actual selected rank output* along
an accepted packed edge, without reflecting its numerical calibration. -/
theorem exact_OpenRankMeasuredPackedEdge (C W : Program 3) (s : Settings)
    (rank : Program 1) (D : Program 2) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty r a b : OTerm α) :
    Nonempty (Derivation B Γ (((acceptEdge (edge4 (rankedExchange C s rank D) W) ctx ty a b) ⊓
      unary rank r a).imp (unary rank r b))) :=
  exact_OpenThinMeasuredEdgePreservesMeasure C s rank D W B α Γ ctx ty r a b

#print axioms exact_OpenRankMeasuredPackedEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeOpenProof
