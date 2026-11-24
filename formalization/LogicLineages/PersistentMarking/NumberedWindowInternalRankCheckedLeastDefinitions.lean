module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeast
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch conjunction constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan (constantOne)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest
  (predecessor equalityTest)

def unaryOn (g : Program 1) (p : Program 3) : Program 3 :=
  .composition g (fun _ : Fin 1 => p)

def seedRank (g : Program 1) : Program 3 := unaryOn g (.projection (2 : Fin 3))
def outputRank (g : Program 1) (least : Program 3) : Program 3 :=
  unaryOn g (unaryOn predecessor least)

def rankEq (g : Program 1) (least : Program 3) : Program 3 :=
  .composition equalityTest (Fin.cons (seedRank g) (Fin.cons (outputRank g least) Fin.elim0))

def rankTest (g : Program 1) (least : Program 3) : Program 3 :=
  conjunction (rankEq g least) (constantOne 3)

/-- On a real success, the same original least result is returned,
but the physical AST also provides an open rank-conservation test.
A failed original result is zero regardless of this test. -/
def checkedLeast (g : Program 1) (least : Program 3) : Program 3 :=
  branch (rankTest g least) (constantZero 3) least

end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeast
