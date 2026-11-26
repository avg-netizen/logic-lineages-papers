module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open InternalLessThan (constantOne)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail chosenCell)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (decodeResult)
open NumberedWindowPositivePathAlgorithm (RawEdge ClassHop)

def applyUnary (outer inner : Program 1) : Program 1 :=
  .composition outer (fun _ : Fin 1 => inner)

def one : Program 1 := constantOne 1
def two : Program 1 := applyUnary .succ one

/-- Arity is checked on the original raw sparse field tail: exactly zero
terminates the encoding, while every preceding cell must actually parse. -/
def exactBody : Nat → Program 1
  | 0 => GorbowPRInternalControl.zeroTest
  | n+1 => conjunction cellGood (applyUnary (exactBody n) cellTail)

def cursor : Nat → Program 1
  | 0 => cellTail
  | n+1 => applyUnary cellTail (cursor n)

def field (n : Nat) : Program 1 := applyUnary cellHead (cursor n)

def nodeGood (tag : Program 1) (arity : Nat) : Program 1 :=
  conjunction cellGood
    (conjunction (.composition equalityTest ![cellHead,tag]) (applyUnary (exactBody arity) cellTail))

def edgeGood : Program 1 := nodeGood one 3
def edgeSource : Program 1 := field 0
def edgeTarget : Program 1 := field 1
def edgeWitness : Program 1 := field 2

def hopGood : Program 1 :=
  conjunction (nodeGood two 2) (applyUnary edgeGood (field 1))
def hopTarget : Program 1 := field 0
def hopSource : Program 1 := applyUnary edgeSource (field 1)
def hopRawTarget : Program 1 := applyUnary edgeTarget (field 1)
def hopWitness : Program 1 := applyUnary edgeWitness (field 1)

def run (p : Program 1) (n : Nat) : Nat := evaluate p (n ::ᵥ nil)

/-- The complete optional ordered list from the same selected parser.
This target is intentionally separate from fixed-arity envelope tests. -/
def selectedNode (n : Nat) : Option (Nat × List Nat) := do
  let (tag,body) ← chosenCell n
  let xs ← decodeResult (run parser body)
  pure (tag,xs)

def selectedEdge (n : Nat) : Option RawEdge :=
  if run edgeGood n = 1 then some (run edgeSource n,run edgeWitness n,run edgeTarget n)
  else none

def selectedHop (n : Nat) : Option ClassHop :=
  if run hopGood n = 1 then
    some (run hopTarget n,run hopSource n,run hopWitness n,run hopRawTarget n)
  else none

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
