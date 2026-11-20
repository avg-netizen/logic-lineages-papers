module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRun
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawTick (chosenTick emitState)

/-- Initial frame option is successor of the actual original ordered
raw tape [q,w,r]. The raw witness is not consumed here. -/
def initialize : Program 3 :=
  emitState (constantZero 3) (.composition .succ (fun _ : Fin 1 =>
    consOf (.projection 0) (consOf (.projection 1) (consOf (.projection 2) (constantZero 3)))))

/-- Actual recursor step sees [prior fuel, previous scratch, initial
scratch]. It runs the existing chosen tick on only its previous value. -/
def step (root other : Program 3) : Program 3 :=
  .composition (chosenTick root other) (fun _ : Fin 1 => .projection 1)

/-- Fuel is first, original encoded scratch second. The recursion starts
at the identical input scratch, not at a new default. -/
def iterateState (root other : Program 3) : Program 2 :=
  .recursion (.projection 0) (step root other)

/-- Same w is used at fuel input and left unchanged on the actual
initial witness slot. Input tape is exactly [q,w,r]. -/
def ownState (root other : Program 3) : Program 3 :=
  .composition (iterateState root other) ![.projection 1,initialize]

def ownRun (root other : Program 3) : Program 3 :=
  .composition cellHead (fun _ : Fin 1 => ownState root other)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRun
