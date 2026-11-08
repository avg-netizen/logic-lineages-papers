module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibration
open InternalApplicationResultStack

/-- The semantic fold is defined by genuine well-founded recursion on the
ORIGINAL TERM PAYLOAD. The reconstructed packed type and all computed outputs
are unrestricted. This definition does not mention a machine, a program,
bounded iteration or a chosen fuel. The imported already checked payload
bound is used only to justify these two recursive calls. -/
def semanticFold (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (value : Nat) : Nat :=
  if h : InternalApplicationValidityStack.tagValue value = 2 ∧ guard value = 1 then
    combine (InternalApplicationValidityStack.domainValue value)
      (InternalApplicationValidityStack.resultTypeValue value)
      (semanticFold guard leaf combine
        (InternalApplicationValidityStack.functionChildValue value))
      (semanticFold guard leaf combine
        (InternalApplicationValidityStack.argumentChildValue value))
  else leaf value
termination_by InternalApplicationValidityStack.payloadValue value
decreasing_by
  all_goals
    have hb := InternalApplicationValidityStackStateProof.applicationPayloadBound value h.1
    simp only [InternalApplicationValidityStackStateProof.functionChildPayload,
      InternalApplicationValidityStackStateProof.argumentChildPayload]
    omega

/-- The structured execution of the EXISTING result-stack transition. It is
used only to state calibration of that AST, never to define semanticFold. -/
def stateIterate (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => stateStep guard leaf combine
      (stateIterate guard leaf combine count state)

/-- Canonical failure or live empty work with an arbitrary entire result
stack. No singleton, output tag, bound or representative premise is imposed. -/
def terminal (state : State) : Prop :=
  state = failedState ∨ (state.status = 1 ∧ state.work = [])

/-- A finite worklist's denotation, structurally recursive on that list. A
visit pushes the separately defined semantic fold value immediately; a finish
pops argument then function and combines in function/argument order. Unknown
frame tags and short finish stacks denote failure. This is not execution of
stateStep: it never opens an application or constructs a new work frame. -/
def workMeaning (fold : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat) :
    List Nat → List Nat → Option (List Nat)
  | [], results => some results
  | frame :: rest, results =>
      let tag := (Nat.unpair frame).1
      let value := (Nat.unpair frame).2
      if tag = 0 then workMeaning fold combine rest (fold value :: results)
      else if tag = 1 then
        match results with
        | argument :: function :: remaining =>
            workMeaning fold combine rest
              (combine (Nat.unpair value).1 (Nat.unpair value).2 function argument :: remaining)
        | _ => none
      else none

/-- The denotation of a complete machine configuration, retaining all output
values and their order. Non-one statuses denote failure, exactly as in the
existing transition. A successful denotation is not an internal proof. -/
def stateMeaning (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (state : State) : Option (List Nat) :=
  if state.status = 1 then
    workMeaning (semanticFold guard leaf combine) combine state.work state.results
  else none

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibration
