module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
open InternalApplicationValidityStack NumberedMultisetNumeric

theorem actualOriginalEncodedStackTransition :
    InternalApplicationValidityStackTargets.ActualOriginalEncodedStackTransition := by
  intro node leaf state
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [transitionValue, encodeState, numbersNumber, stateStep]
    | cons value rest =>
      by_cases ht : tagValue value = 2 <;>
        by_cases hn : node (resultTypeValue value) = 1 <;>
        by_cases hl : leaf value = 1 <;>
        simp [transitionValue, encodeState, numbersNumber, stateStep, failedState,
          ht, hn, hl, Nat.add_comm 1, hz]
  · simp [transitionValue, encodeState, stateStep, failedState, numbersNumber, hs, hz]

theorem applicationPayloadBound (value : Nat) (h : tagValue value = 2) :
    functionPayloadValue value + argumentPayloadValue value + 2 ≤ payloadValue value := by
  have h1 := Nat.unpair_add_le (payloadValue value)
  have h2 := Nat.unpair_right_le (bodyValue value)
  have h3 := Nat.unpair_add_le (Nat.unpair (bodyValue value)).2
  change tagValue value + bodyValue value ≤ payloadValue value at h1
  change functionPayloadValue value + argumentPayloadValue value ≤
    (Nat.unpair (bodyValue value)).2 at h3
  omega

theorem workWeightCons (value : Nat) (rest : List Nat) :
    workWeight (value :: rest) = payloadValue value + 1 + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

theorem functionChildPayload (value : Nat) :
    payloadValue (functionChildValue value) = functionPayloadValue value := by
  simp [functionChildValue, functionValue, payloadValue]

theorem argumentChildPayload (value : Nat) :
    payloadValue (argumentChildValue value) = argumentPayloadValue value := by
  simp [argumentChildValue, argumentValue, payloadValue]

theorem actualOriginalStackWorkDecrease :
    InternalApplicationValidityStackTargets.ActualOriginalStackWorkDecrease := by
  intro node leaf state hs hw
  rcases state with ⟨s, xs⟩
  simp only at hs hw
  subst s
  cases xs with
  | nil => exact False.elim (hw rfl)
  | cons value rest =>
    by_cases ht : tagValue value = 2
    · have hb := applicationPayloadBound value ht
      by_cases hn : node (resultTypeValue value) = 1
      · simp only [stateStep, ht, hn, if_true, workWeightCons, functionChildPayload,
          argumentChildPayload]
        omega
      · simp [stateStep, ht, hn, failedState, workWeightCons, workWeight]
    · by_cases hl : leaf value = 1
      · simp only [stateStep, ht, hl, if_true, if_false, workWeightCons]
        omega
      · simp [stateStep, ht, hl, failedState, workWeightCons, workWeight]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
