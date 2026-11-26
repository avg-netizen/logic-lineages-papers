module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallback
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch constantZero)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw termShape chosenFrame)
open NumberedWindowInternalSparseRawTick (tagFiveTest)

/-- Expose the exact auxiliary source in the fall-through dispatcher.
At an auxiliary application only tag five can supply a contextual
frame. Keep the original callback unchanged for every other source. -/
def sourceIsAux : Program 3 := onRaw termShape 0

def auxiliaryFallback (other : Program 3) : Program 3 :=
  branch sourceIsAux other (branch tagFiveTest (constantZero 3) chosenFrame)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallback
