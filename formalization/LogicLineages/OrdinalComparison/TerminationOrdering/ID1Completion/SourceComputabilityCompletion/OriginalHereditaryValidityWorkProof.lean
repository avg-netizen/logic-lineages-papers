module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
open OriginalHereditaryValidity

/-- Every raw application payload pays for both actual child payloads. -/
theorem applicationPayloadBound (value : Nat) (h : tagValue value = 2) :
    functionPayloadValue value + argumentPayloadValue value + 2 ≤ payloadValue value := by
  have h1 := Nat.unpair_add_le (payloadValue value)
  have h2 := Nat.unpair_right_le (InternalApplicationValidityStack.bodyValue value)
  have h3 := Nat.unpair_add_le
    (Nat.unpair (InternalApplicationValidityStack.bodyValue value)).2
  change tagValue value + InternalApplicationValidityStack.bodyValue value ≤
    payloadValue value at h1
  change functionPayloadValue value + argumentPayloadValue value ≤
    (Nat.unpair (InternalApplicationValidityStack.bodyValue value)).2 at h3
  omega

/-- Literal lambda tag one pays for the body, regardless of its type or Gamma. -/
theorem lambdaPayloadBound (value : Nat) (h : tagValue value = 1) :
    lambdaBodyPayloadValue value + 1 ≤ payloadValue value := by
  have h1 := Nat.unpair_add_le (payloadValue value)
  have h2 := Nat.unpair_right_le (Nat.unpair (payloadValue value)).2
  change tagValue value + (Nat.unpair (payloadValue value)).2 ≤
    payloadValue value at h1
  change lambdaBodyPayloadValue value ≤ (Nat.unpair (payloadValue value)).2 at h2
  omega

theorem actualOriginalHereditaryPayloadBounds :
    OriginalHereditaryValidityTargets.ActualOriginalHereditaryPayloadBounds :=
  ⟨applicationPayloadBound, lambdaPayloadBound⟩

theorem workWeightCons (frame : Frame) (rest : List Frame) :
    workWeight (frame :: rest) = payloadValue frame.raw + 1 + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

theorem functionChildPayload (value : Nat) :
    payloadValue (functionChildValue value) = functionPayloadValue value := by
  simp [functionChildValue, InternalApplicationValidityStack.functionChildValue,
    InternalApplicationValidityStack.functionValue, payloadValue,
    InternalApplicationValidityStack.payloadValue]

theorem argumentChildPayload (value : Nat) :
    payloadValue (argumentChildValue value) = argumentPayloadValue value := by
  simp [argumentChildValue, InternalApplicationValidityStack.argumentChildValue,
    InternalApplicationValidityStack.argumentValue, payloadValue,
    InternalApplicationValidityStack.payloadValue]

theorem lambdaChildPayload (value : Nat) :
    payloadValue (lambdaBodyValue value) = lambdaBodyPayloadValue value := by
  simp [lambdaBodyValue, payloadValue, InternalApplicationValidityStack.payloadValue]

/-- Parameters travel with each frame but do not contribute to this measure. -/
theorem actualOriginalHereditaryWorkDecrease :
    OriginalHereditaryValidityTargets.ActualOriginalHereditaryWorkDecrease := by
  intro oldSource oldTarget member state hs hw
  rcases state with ⟨s, xs⟩
  simp only at hs hw
  subst s
  cases xs with
  | nil => exact False.elim (hw rfl)
  | cons frame rest =>
    by_cases hc : nodeCheckValue oldSource oldTarget member frame.raw frame.parameter = 1
    · by_cases ht : tagValue frame.raw = 2
      · have hb := applicationPayloadBound frame.raw ht
        simp only [stateStep, hc, ht, if_true, workWeightCons,
          functionChildPayload, argumentChildPayload]
        omega
      · by_cases hl : tagValue frame.raw = 1
        · have hb := lambdaPayloadBound frame.raw hl
          have h12 : (1 : Nat) ≠ 2 := by omega
          simp only [stateStep, hc, hl, h12, if_true, if_false, workWeightCons,
            lambdaChildPayload]
          omega
        · simp only [stateStep, hc, ht, hl, if_true, if_false, workWeightCons]
          omega
    · simp [stateStep, hc, failedState, workWeightCons, workWeight]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
