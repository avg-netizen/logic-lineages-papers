module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest (predecessor)

def unaryAfter {n : Nat} (g : Program 1) (A : Program n) : Program n :=
  .composition g (fun _ : Fin 1 => A)

def resultRank {n : Nat} (g : Program 1) (A : Program n) : Program n :=
  unaryAfter g (unaryAfter predecessor A)

/-- Filter the actual successful optional output. A rejected zero
result is kept zero on either branch. No raw row is changed. -/
def zeroOutput {n : Nat} (g : Program 1) (A : Program n) : Program n :=
  branch (resultRank g A) A (constantZero n)

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvance
