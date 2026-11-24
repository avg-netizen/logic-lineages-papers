module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest (equalityTest)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)

def atSlot (M : Program 1) (i : Fin 2) : Program 2 :=
  .composition M (fun _ : Fin 1 => .projection i)

def compareMeasurements (M : Program 1) : Program 2 :=
  .composition equalityTest ![atSlot M 0,atSlot M 1]

def measuredExchange (M : Program 1) (X : Program 2) : Program 2 :=
  conjunction X (compareMeasurements M)

def ExactMeasuredExchangeCalibration : Prop :=
  ∀ (s : Settings) (M : Program 1) (X : Program 2),
    TermMeasureCalibrated M → ActualTermExchange s X → ActualTermExchange s (measuredExchange M X)

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinDefinitions
