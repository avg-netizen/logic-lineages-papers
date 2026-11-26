module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecode
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion

/-- Square of the certified floor root of the sparse input code. -/
def rootSquare : Program 1 :=
  .composition InternalArithmeticPrograms.multiplication
    ![InternalSquareRoot.root,InternalSquareRoot.root]

/-- Subtraction reads [subtrahend,minuend], so this is n-root(n)^2. -/
def leftCandidate : Program 1 :=
  .composition InternalEqualityTest.subtract ![rootSquare,.projection 0]

def rightCandidate : Program 1 :=
  .composition InternalEqualityTest.subtract ![leftCandidate,InternalSquareRoot.root]

/-- Unlike a total max-square decoder, this parser must reject the gap:
its residual is strictly larger than its floor root. -/
def gap : Program 1 :=
  .composition InternalLessThan.ltTest ![InternalSquareRoot.root,leftCandidate]

def good : Program 1 :=
  InternalAcceptance.branch gap (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)

def chosenDecode (n : Nat) : Option (Nat × Nat) :=
  let xs := n ::ᵥ nil
  if evaluate good xs = 1 then some (evaluate leftCandidate xs,evaluate rightCandidate xs)
  else none

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecode
