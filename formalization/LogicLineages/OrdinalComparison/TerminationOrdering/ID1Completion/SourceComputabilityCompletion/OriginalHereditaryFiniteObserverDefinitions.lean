module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Finite semantic observation layers, not raw scheduler visits. Argument-list
administration does not consume a layer. No dynamic evaluator or tuple is changed. -/
def family (R : Program 2) : Nat → Program 2
 | 0 => R
 | depth+1 => OriginalHereditaryObservationLayer.layer R (family R depth)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserver
