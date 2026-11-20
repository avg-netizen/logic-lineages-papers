module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowRawContextAlgorithm (Frame)
open NumberedWindowFieldAlgorithm (pack unpackNode)

def onRaw (p : Program 1) (i : Fin 3) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection i)

def frameSlot (n : Nat) (i : Fin 3) : Program 3 := onRaw (field n) i
def sameSlot (n : Nat) : Program 3 := .composition equalityTest ![frameSlot n 0,frameSlot n 2]

def witnessShape : Program 1 := nodeGood (literal 1 5) 1
def termShape : Program 1 := nodeGood (literal 1 6) 4

/-- Input tape is exactly [raw source, raw witness, raw destination].
The only two permitted term nodes are the literal auxiliary application
constructors. Slots 0, 1, 3 of their raw fields must actually agree. -/
def frameGood : Program 3 :=
  conjunction (onRaw witnessShape 1)
    (conjunction (onRaw termShape 0)
      (conjunction (onRaw termShape 2)
        (conjunction (sameSlot 0) (conjunction (sameSlot 1) (sameSlot 3)))))

/-- Private scratch row [source function, *actual witness child*,
destination function]. The optional value is successor-packed; 0
means reject rather than a default child. The raw child is unchanged. -/
def emitFrame : Program 3 :=
  .composition .succ (fun _ : Fin 1 =>
    consOf (frameSlot 2 0) (consOf (frameSlot 0 1) (consOf (frameSlot 2 2) (constantZero 3))))

def chosenFrame : Program 3 := branch frameGood (constantZero 3) emitFrame

def encodeFrame : Option Frame → Nat
  | none => 0
  | some (q,w,r) => pack [q,w,r] + 1

/-- The actual original branch of the raw tick, not a new relation.
Other witness tags belong to other tick branches and return none here. -/
def tagFiveNext (q w r : Nat) : Option Frame :=
  match unpackNode w with
  | some (5,[child]) => NumberedWindowRawContextAlgorithm.next 5 [child] q r
  | _ => none

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrame
