module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecode
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCell
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowInternalSparseDecode (good leftCandidate rightCandidate)
open NumberedWindowFieldAlgorithm (State)

def atPredecessor (p : Program 1) : Program 1 :=
  .composition p (fun _ => InternalEqualityTest.predecessor)

def cellGood : Program 1 :=
  InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
    (atPredecessor good)

def cellHead : Program 1 := atPredecessor leftCandidate

def cellTail : Program 1 := atPredecessor rightCandidate

/-- A zero code is nil, not an encoded cell. A nonzero sparse gap also
returns none; the existing field state machine still distinguishes nil. -/
def chosenCell (n : Nat) : Option (Nat × Nat) :=
  let xs := n ::ᵥ nil
  if evaluate cellGood xs = 1 then some (evaluate cellHead xs,evaluate cellTail xs)
  else none

def chosenStep : State → State
  | none => none
  | some (0,acc) => some (0,acc)
  | some (n+1,acc) => (chosenCell (n+1)).map (fun ht => (ht.2,ht.1 :: acc))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCell
