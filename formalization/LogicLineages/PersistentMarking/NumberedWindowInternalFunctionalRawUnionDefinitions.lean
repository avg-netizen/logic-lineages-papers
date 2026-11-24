module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppend (append)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalDirectTypedListTargets (parsedPayload)

def side (i : Fin 2) : Program 2 := .composition parsedPayload ![.projection i]
def joinedScratch : Program 2 := .composition append ![side 0,side 1]

/-- Canonical ordered raw union: the original positive parser payloads,
the original scratch append, and the literal sparse repacker. -/
def functionalUnion : Program 2 := .composition repack ![joinedScratch]

end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnion
