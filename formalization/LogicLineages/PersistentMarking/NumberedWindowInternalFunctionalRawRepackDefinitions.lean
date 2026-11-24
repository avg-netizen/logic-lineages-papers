module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepack
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursion (listRec)
open NumberedWindowInternalSparsePair (fieldCons)

/-- Read the original scratch list as-is, rebuilding its cells with the
actual sparse raw constructor, not the scratch-pair constructor. -/
def repack : Program 1 := listRec (.zero : Program 0) fieldCons

end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepack
