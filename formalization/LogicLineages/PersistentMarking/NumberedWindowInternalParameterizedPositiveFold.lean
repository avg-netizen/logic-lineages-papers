module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalLessThan (constantOne)
open InternalListCodec (consCode headCode tailCode)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePositiveFold (initial scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)

def advanceAt (A : Program 4) : Program 6 :=
  .composition A ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]

def updateAt (A : Program 4) : Program 6 :=
  .composition consCode ![onCursor cellTail,advanceAt A]

def stepAt (A : Program 4) : Program 6 :=
  branch scratchCursor (.projection 1) (branch (onCursor cellGood) dead (updateAt A))

def iterateAt (A : Program 4) : Program 5 := .recursion initial (stepAt A)

def stateAt (A : Program 4) : Program 4 :=
  .composition (iterateAt A) ![.projection 3,.projection 0,.projection 1,.projection 2,.projection 3]

def finishAt (A : Program 4) : Program 4 :=
  let state := stateAt A
  let left := .composition headCode (fun _ : Fin 1 => state)
  let actual := .composition tailCode (fun _ : Fin 1 => state)
  branch left actual (constantZero 4)

def walkAt (A : Program 4) : Program 5 :=
  let source := .composition .succ (fun _ : Fin 1 => .projection (2 : Fin 5))
  .composition (finishAt A) ![.projection 0,.projection 1,source,.projection 3]

def positiveAt (A : Program 4) : Program 5 :=
  let nonempty := branch (.projection 3) (constantZero 5) (constantOne 5)
  let target := .composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))
  conjunction nonempty (.composition equalityTest ![walkAt A,target])

/-- Only the actual per-cell callback is supplied. This definitional
specialization keeps the original scratch state, physical parser,
certificate-derived fuel, tape fields and final positive test. -/
theorem exact_OriginalParameterizedPositive (raw : Program 5) (L : Program 3) :
    positiveAt (advance raw L) = NumberedWindowInternalSparsePositiveFold.positive raw L := rfl

def zeroPositive (g : Program 1) (raw : Program 5) (L : Program 3) : Program 5 :=
  positiveAt (zeroOutput g (advance raw L))

#print axioms exact_OriginalParameterizedPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
