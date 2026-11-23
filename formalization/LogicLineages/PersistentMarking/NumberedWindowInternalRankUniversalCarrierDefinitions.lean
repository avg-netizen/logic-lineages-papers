module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrier
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (conjunction)
open NumberedWindowInternalAtomicRefinement (atTarget)
open NumberedWindowInternalNeutralRankGuard (rankEven)

/-- The actual scalar call is retained at every destination, including
when the original source is not a neutral term. -/
def alwaysCarried (i : Program 1) (r : Program 3) : Program 3 :=
  conjunction r (atTarget i)

def completeRankEven (i g : Program 1) (r : Program 3) : Program 3 :=
  rankEven i g (alwaysCarried i r)

end LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrier
