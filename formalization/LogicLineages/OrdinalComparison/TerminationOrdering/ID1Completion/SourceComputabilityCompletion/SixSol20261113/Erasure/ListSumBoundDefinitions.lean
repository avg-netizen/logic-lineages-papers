module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual original listRec sum with identity weight, including multiplicities.
No decoded list, multiset membership, or altered sorting program is introduced. -/
def sum : Program 1 := SortWeightedDefinitions.weighted (.projection (0 : Fin 1))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundDefinitions
