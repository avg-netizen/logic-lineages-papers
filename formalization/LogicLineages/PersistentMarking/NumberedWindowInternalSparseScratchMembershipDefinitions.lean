module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalEqualityTest (equalityTest)
open InternalLessThan (constantOne)
open InternalRawListRecursion (listRec)

/-- Nil always rejects; the candidate is not read as a default head. -/
def memberBase : Program 1 := constantZero 1

/-- The literal row tape is [head, tail membership bit, candidate]. -/
def headMatches : Program 3 :=
  .composition equalityTest ![.projection 0,.projection 2]

/-- On the real head equality return one; otherwise retain the actual
tail result at the same candidate. Nothing changes the original list. -/
def memberStep : Program 3 :=
  branch headMatches (.projection 1) (constantOne 3)

/-- Original arity-two list recursion on [standard scratch code,candidate].
This program is not an unpacker for the separate sparse polynomial codec. -/
def scratchMember : Program 2 :=
  listRec memberBase memberStep

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembership
