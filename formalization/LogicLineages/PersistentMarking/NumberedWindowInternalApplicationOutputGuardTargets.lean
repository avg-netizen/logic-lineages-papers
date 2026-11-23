module

public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (conjunction)
open NumberedWindowGuardedGraphTargets (atSlot)

/-- A new physical selection, not a change to the old application checker. -/
def outputGuard (i : Program 1) (p : Program 3) : Program 3 :=
  conjunction p (atSlot i 2)

end LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardTargets
