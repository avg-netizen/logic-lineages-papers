module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCell
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero branch)
open InternalLessThan (constantOne)
open InternalEqualityTest (predecessor subtract)
open InternalListCodec (consCode headCode)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)

-- Scratch storage only. The originals' raw cell numbers are not changed.
def scratchBase (B : Program 2) : Program 2 :=
  .composition consCode ![B,constantZero 2]

def scratchStep (R : Program 4) : Program 4 :=
  .composition consCode ![R,.projection 1]

def scratchTable (B : Program 2) (R : Program 4) : Program 3 :=
  .recursion (scratchBase B) (scratchStep R)

def scratchRow (B : Program 2) (R : Program 4) : Program 3 :=
  .composition headCode (fun _ : Fin 1 => scratchTable B R)

/-- A decoder row is zero on failure, or a successor of the scratch
ordered-list code. The decoded scratch field is not a source raw code. -/
def prependPayload : Program 2 :=
  let tail := .composition predecessor (fun _ : Fin 1 => .projection (1 : Fin 2))
  let cons := .composition consCode ![.projection 0,tail]
  .composition .succ (fun _ : Fin 1 => cons)

def prependResult : Program 2 :=
  branch (.projection 1) (constantZero 2) prependPayload

/-- Inputs are [prior index, complete prior scratch table, fixed parameter 0,
fixed parameter 1]. A raw successor cell is at index+1. -/
def nextRaw : Program 4 :=
  .composition .succ (fun _ : Fin 1 => .projection (0 : Fin 4))

def atRaw (p : Program 1) : Program 4 :=
  .composition p (fun _ : Fin 1 => nextRaw)

def tailLag : Program 4 :=
  .composition subtract ![atRaw cellTail,.projection 0]

def priorResult : Program 4 :=
  .composition lookup ![tailLag,.projection 1]

def onCell : Program 4 :=
  .composition prependResult ![atRaw cellHead,priorResult]

def parserBase : Program 2 := constantOne 2

def parserStep : Program 4 :=
  branch (atRaw cellGood) (constantZero 4) onCell

/-- The two scratch parameters are pinned to zero; the sole external input
is the unchanged original raw polynomial field-list code. -/
def parser : Program 1 :=
  .composition (scratchRow parserBase parserStep) ![.projection 0,constantZero 1,constantZero 1]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
