module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachine
open OriginalHereditaryValidity

/-- Native finite acceptance trees for precisely the existing machine's
raw selectors and per-frame parameters. This is only a proof intermediary;
the final recurrence concerns the unchanged bounded validator itself. -/
inductive NativeAccepted (oldSource oldTarget member : Nat → Nat → Nat) : Nat → Nat → Prop
  | application {value parameter : Nat} :
      nodeCheckValue oldSource oldTarget member value parameter = 1 →
      tagValue value = 2 →
      NativeAccepted oldSource oldTarget member (functionChildValue value) parameter →
      NativeAccepted oldSource oldTarget member (argumentChildValue value) parameter →
      NativeAccepted oldSource oldTarget member value parameter
  | lambda {value parameter : Nat} :
      nodeCheckValue oldSource oldTarget member value parameter = 1 →
      tagValue value = 1 →
      NativeAccepted oldSource oldTarget member
        (lambdaBodyValue value) (childParameterValue value parameter) →
      NativeAccepted oldSource oldTarget member value parameter
  | other {value parameter : Nat} :
      nodeCheckValue oldSource oldTarget member value parameter = 1 →
      tagValue value ≠ 2 → tagValue value ≠ 1 →
      NativeAccepted oldSource oldTarget member value parameter

/-- No new Program: this is the structured iteration of the existing step. -/
def stateIterate (oldSource oldTarget member : Nat → Nat → Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state =>
      stateStep oldSource oldTarget member (stateIterate oldSource oldTarget member count state)

def terminal (state : State) : Prop :=
  state = failedState ∨ state = (⟨1, []⟩ : State)

def stateAccepted (oldSource oldTarget member : Nat → Nat → Nat) (state : State) : Prop :=
  state.status = 1 ∧ ∀ frame ∈ state.work,
    NativeAccepted oldSource oldTarget member frame.raw frame.parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachine
