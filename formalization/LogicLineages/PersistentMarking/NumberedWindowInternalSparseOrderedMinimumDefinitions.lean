module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero branch)
open InternalEqualityTest (predecessor)
open InternalLessThan (ltTest)
open InternalRawListRecursion (listRec)
open NumberedWindowInternalSparseFieldParser (parser)

/-- Actual [head, encoded-tail-min] tape. Success stores successor of
the code, so an actual head of zero is a nonempty successful offer. -/
def offerHead : Program 2 :=
  .composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2))

def preferHead : Program 2 :=
  .composition ltTest ![offerHead,.projection 1]

/-- No prior result selects the original head. Otherwise compare the
actual two successor-encoded values and retain one of them. Equal
values retain the tail result; this never drops the ordered input list. -/
def minimumStep : Program 2 :=
  branch (.projection 1) offerHead (branch preferHead (.projection 1) offerHead)

/-- This recursor works on the standard Nat.pair scratch list, not
directly on sparse polynomial original input cells. It has no parameters. -/
def scratchMinimum : Program 1 :=
  listRec (constantZero 0) minimumStep

def decodedScratch : Program 1 :=
  .composition predecessor (fun _ : Fin 1 => parser)

def parsedMinimum : Program 1 :=
  .composition scratchMinimum (fun _ : Fin 1 => decodedScratch)

/-- The actual sparse parser is the only entrance to the scratch
recursion. Parser failure goes to none, not a substitute scratch list. -/
def orderedPoolMinimum : Program 1 :=
  branch parser (constantZero 1) parsedMinimum

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimum
