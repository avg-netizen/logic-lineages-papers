module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineInvariantProof
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrenceMachine

theorem nativeAcceptanceEquation (oldSource oldTarget member : Nat → Nat → Nat)
    (value parameter : Nat) :
    NativeAccepted oldSource oldTarget member value parameter ↔
      nodeCheckValue oldSource oldTarget member value parameter = 1 ∧
        (if tagValue value = 2 then
          NativeAccepted oldSource oldTarget member (functionChildValue value) parameter ∧
            NativeAccepted oldSource oldTarget member (argumentChildValue value) parameter
        else if tagValue value = 1 then
          NativeAccepted oldSource oldTarget member
            (lambdaBodyValue value) (childParameterValue value parameter)
        else True) := by
  constructor
  · intro h
    cases h with
    | application hc ht hf ha => simp [hc, ht, hf, ha]
    | lambda hc ht hb => simp [hc, ht, hb]
    | other hc ha hl => simp [hc, ha, hl]
  · rintro ⟨hc, hchildren⟩
    by_cases ha : tagValue value = 2
    · have hpair :
          NativeAccepted oldSource oldTarget member (functionChildValue value) parameter ∧
            NativeAccepted oldSource oldTarget member (argumentChildValue value) parameter := by
        simpa only [ha, if_true] using hchildren
      exact .application hc ha hpair.1 hpair.2
    · by_cases hl : tagValue value = 1
      · have hb : NativeAccepted oldSource oldTarget member
            (lambdaBodyValue value) (childParameterValue value parameter) := by
          simpa only [if_neg ha, if_pos hl] using hchildren
        exact .lambda hc hl hb
      · exact .other hc ha hl

/-- Every step preserves the conjunction of native acceptance trees over
its literal pending frames. Rejection and all other statuses are included. -/
theorem stepInvariant (oldSource oldTarget member : Nat → Nat → Nat) (state : State) :
    stateAccepted oldSource oldTarget member (stateStep oldSource oldTarget member state) ↔
      stateAccepted oldSource oldTarget member state := by
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [stateStep, stateAccepted]
    | cons frame rest =>
      have he := nativeAcceptanceEquation oldSource oldTarget member frame.raw frame.parameter
      by_cases hc : nodeCheckValue oldSource oldTarget member frame.raw frame.parameter = 1 <;>
        by_cases ha : tagValue frame.raw = 2 <;>
        by_cases hl : tagValue frame.raw = 1 <;>
        simp [stateStep, stateAccepted, failedState, hc, ha, hl, he, and_assoc]
  · simp [stateStep, stateAccepted, failedState, hs]

theorem iterateInvariant (oldSource oldTarget member : Nat → Nat → Nat)
    (count : Nat) (state : State) :
    stateAccepted oldSource oldTarget member
        (stateIterate oldSource oldTarget member count state) ↔
      stateAccepted oldSource oldTarget member state := by
  induction count with
  | zero => exact Iff.rfl
  | succ count ih =>
    exact (stepInvariant oldSource oldTarget member
      (stateIterate oldSource oldTarget member count state)).trans ih

theorem terminalAcceptance (oldSource oldTarget member : Nat → Nat → Nat)
    (state : State) (ht : terminal state) :
    (state.status = 1 ∧ state.work = []) ↔ stateAccepted oldSource oldTarget member state := by
  rcases ht with rfl | rfl <;> simp [stateAccepted, failedState]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineInvariantProof
