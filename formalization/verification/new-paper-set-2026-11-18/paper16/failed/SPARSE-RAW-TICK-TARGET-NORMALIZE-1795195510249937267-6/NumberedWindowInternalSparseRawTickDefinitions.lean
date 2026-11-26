module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTick
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch normalize constantZero)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (applyUnary field nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalFreshProbeDispatchProgram (literal predOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowRawContextAlgorithm (Frame State next)
open NumberedWindowFieldAlgorithm (pack unpackNode)

/-- Complete original contextual fallback. Its output uses the same
private optional scratch row, and none stays 0. No raw graph premise. -/
def fallbackValue (q w r : Nat) : Option Frame := do
  let (tag,fields) ← unpackNode w
  next tag fields q r

def encodeState (s : State) : Nat := pack [s.1.toNat,encodeFrame s.2]

def emitState {n : Nat} (flag frame : Program n) : Program n :=
  consOf flag (consOf frame (constantZero n))

def rootTest : Program 3 := onRaw (nodeGood (literal 1 0) 1) 1
def tagFiveTest : Program 3 := onRaw witnessShape 1

def rootCall (root : Program 3) : Program 3 :=
  normalize (.composition root ![.projection 0,frameSlot 0 1,.projection 2])

/-- Literal tape [source,witness,destination]. Only the real root branch
can set a success flag, and it emits no frame. Every context branch,
including the actual tag5 branch and rejected input, emits flag zero. -/
def liveTick (root other : Program 3) : Program 3 :=
  branch tagFiveTest
    (branch rootTest (emitState (constantZero 3) other)
      (emitState (rootCall root) (constantZero 3)))
    (emitState (constantZero 3) chosenFrame)

/-- Private scratch state is raw pack [flag,frameOption]. The first
physical cell contains the flag, the second the optional frame code. -/
def stateFrame : Program 1 := field 0
def rowBody : Program 1 := applyUnary predOne stateFrame
def rowSource : Program 1 := applyUnary cellHead rowBody
def rowWitness : Program 1 := applyUnary cellHead (applyUnary cellTail rowBody)
def rowDestination : Program 1 :=
  applyUnary cellHead (applyUnary cellTail (applyUnary cellTail rowBody))

def performLive (root other : Program 3) : Program 1 :=
  .composition (liveTick root other) ![rowSource,rowWitness,rowDestination]

/-- Terminal states preserve their one actual state code, not rebuilt
defaults. When a frame is live the old flag is intentionally ignored. -/
def chosenTick (root other : Program 3) : Program 1 :=
  branch stateFrame (.projection 0) (performLive root other)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTick
