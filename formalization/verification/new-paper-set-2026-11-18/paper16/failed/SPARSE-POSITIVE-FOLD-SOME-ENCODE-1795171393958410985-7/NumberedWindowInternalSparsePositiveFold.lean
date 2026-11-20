module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvance
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalLessThan (constantOne)
open InternalListCodec (consCode headCode tailCode)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathAdvance (advance)

/-- This pair is private scratch state [remaining RAW cursor, encoded
current Option]. The old certificate and its tail are never repacked in
this scratch codec. Base parameters are [context,type,initial,certificate]. -/
def initial : Program 4 := .composition consCode ![.projection 3,.projection 2]

/-- The step sees [old fuel counter, old scratch state,context,type,
initial,certificate]. It does not reinterpret the fuel as a raw code. -/
def scratchCursor : Program 6 :=
  .composition headCode (fun _ : Fin 1 => .projection 1)
def scratchCurrent : Program 6 :=
  .composition tailCode (fun _ : Fin 1 => .projection 1)
def onCursor (p : Program 1) : Program 6 :=
  .composition p (fun _ : Fin 1 => scratchCursor)

def advanceAtCell (raw : Program 5) (least : Program 3) : Program 6 :=
  .composition (advance raw least) ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]

def updateCell (raw : Program 5) (least : Program 3) : Program 6 :=
  .composition consCode ![onCursor cellTail,advanceAtCell raw least]

def dead : Program 6 := .composition consCode ![constantZero 6,constantZero 6]

def iterateStep (raw : Program 5) (least : Program 3) : Program 6 :=
  branch scratchCursor (.projection 1) (branch (onCursor cellGood) dead (updateCell raw least))

/-- Coordinates [fuel, packed context, type, encoded current, original raw
certificate]. Each successor consumes one cell at most, in original head
first order. After nil or malformed input the scratch state stabilizes. -/
def iterateState (raw : Program 5) (least : Program 3) : Program 5 :=
  .recursion initial (iterateStep raw least)

/-- Choose precisely the original certificate as the fuel, retaining that
same unmodified raw code in the initial state's original cursor. -/
def chosenState (raw : Program 5) (least : Program 3) : Program 4 :=
  .composition (iterateState raw least)
    ![.projection 3,.projection 0,.projection 1,.projection 2,.projection 3]

def finish (raw : Program 5) (least : Program 3) : Program 4 :=
  let state := chosenState raw least
  let left := .composition headCode (fun _ : Fin 1 => state)
  let actual := .composition tailCode (fun _ : Fin 1 => state)
  branch left actual (constantZero 4)

def chosenWalk (raw : Program 5) (least : Program 3) : Program 5 :=
  let encodeSource := .composition .succ (fun _ : Fin 1 => .projection (2 : Fin 5))
  .composition (finish raw least) ![.projection 0,.projection 1,encodeSource,.projection 3]

/-- The original positive checker does not accept an empty path even when
its initial and destination classes already agree. -/
def positive (raw : Program 5) (least : Program 3) : Program 5 :=
  let nonempty := branch (.projection 3) (constantZero 5) (constantOne 5)
  let encodeTarget := .composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))
  conjunction nonempty (.composition equalityTest ![chosenWalk raw least,encodeTarget])

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold
