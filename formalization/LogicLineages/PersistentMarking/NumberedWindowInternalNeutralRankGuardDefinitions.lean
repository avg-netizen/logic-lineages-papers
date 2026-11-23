module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch conjunction constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan
  (ltTest constantOne)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)

/-- Actual positive rank of the output on the original three fields. -/
def targetHasRank (g : Program 1) : Program 3 :=
  branch (atTarget g) (constantZero 3) (constantOne 3)

def lowersRank (g : Program 1) : Program 3 :=
  .composition ltTest ![atTarget g,atSource g]

/-- Do not change the old calculator when the source has rank zero.
Every positively ranked success supplies both the smaller positive
rank and the original scalar carrier of the actual y. -/
def rankEven (i g : Program 1) (r : Program 3) : Program 3 :=
  branch (atSource g) r
    (conjunction r (conjunction (targetHasRank g) (conjunction (atTarget i) (lowersRank g))))

/-- Positive-rank functions produce positive-rank carried outputs.
This is a candidate physical guard, not a conclusion about its numerical
equivalence with the original application graph. -/
def rankApplication (i g : Program 1) (p : Program 3) : Program 3 :=
  branch (atSource g) p (conjunction p (conjunction (targetHasRank g) (atTarget i)))

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuard
