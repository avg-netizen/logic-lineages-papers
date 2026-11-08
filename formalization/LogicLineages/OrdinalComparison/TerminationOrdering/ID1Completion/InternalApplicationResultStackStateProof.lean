module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackStateProof
open InternalApplicationResultStack NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalEncodedResultStackTransition :
    InternalApplicationResultStackTargets.ActualOriginalEncodedResultStackTransition := by
  intro guard leaf combine state
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [transitionValue, encodeState, numbersNumber, stateStep]
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · by_cases ho : InternalApplicationValidityStack.tagValue (Nat.unpair frame).2 = 2 ∧
            guard (Nat.unpair frame).2 = 1 <;>
          simp [transitionValue, encodeState, numbersNumber, stateStep, ht, ho, Nat.add_comm 1]
      · by_cases hf : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [transitionValue, encodeState, numbersNumber, stateStep, ht, hf, failedState, hz]
          | cons a ys =>
            cases ys with
            | nil => simp [transitionValue, encodeState, numbersNumber, stateStep, ht, hf, failedState, hz,
                Nat.add_comm 1]
            | cons f ys => simp [transitionValue, encodeState, numbersNumber, stateStep, ht, hf,
                Nat.add_comm 1]
        · simp [transitionValue, encodeState, numbersNumber, stateStep, ht, hf, failedState, hz,
            Nat.add_comm 1]
  · simp [transitionValue, encodeState, stateStep, failedState, numbersNumber, hs, hz]

theorem workWeightCons (frame : Nat) (rest : List Nat) :
    workWeight (frame :: rest) = frameWeight frame + workWeight rest := by
  simp only [workWeight, List.map_cons, List.sum_cons]

theorem visitWeight (value : Nat) :
    frameWeight (visitValue value) = fuelValue value := by
  simp [frameWeight, visitValue, fuelValue]

theorem finishWeight (d e : Nat) : frameWeight (finishValue d e) = 1 := by
  simp [frameWeight, finishValue]

theorem actualOriginalResultStackWorkDecrease :
    InternalApplicationResultStackTargets.ActualOriginalResultStackWorkDecrease := by
  intro guard leaf combine state hs hw
  rcases state with ⟨s, xs, ys⟩
  simp only at hs hw
  subst s
  cases xs with
  | nil => exact False.elim (hw rfl)
  | cons frame rest =>
    by_cases ht : (Nat.unpair frame).1 = 0
    · by_cases ho : InternalApplicationValidityStack.tagValue (Nat.unpair frame).2 = 2 ∧
          guard (Nat.unpair frame).2 = 1
      · have hb := InternalApplicationValidityStackStateProof.applicationPayloadBound
          (Nat.unpair frame).2 ho.1
        simp only [stateStep, ht, ho, and_self, if_true, workWeightCons, visitWeight, finishWeight,
          fuelValue, InternalApplicationValidityStackStateProof.functionChildPayload,
          InternalApplicationValidityStackStateProof.argumentChildPayload]
        simp only [frameWeight, ht, if_true]
        omega
      · simp only [stateStep, ht, ho, and_self, if_true, if_false, workWeightCons, frameWeight]
        omega
    · by_cases hf : (Nat.unpair frame).1 = 1
      · cases ys with
        | nil => simp [stateStep, ht, hf, failedState, workWeight, frameWeight]
        | cons a ys =>
          cases ys with
          | nil => simp [stateStep, ht, hf, failedState, workWeight, frameWeight]
          | cons f ys => simp [stateStep, ht, hf, workWeightCons, frameWeight]
      · simp [stateStep, ht, hf, failedState, workWeight, frameWeight]

theorem fuelEvaluation (value : Nat) :
    evaluate fuel (List.Vector.ofFn ![value]) = fuelValue value := by
  change (evaluate InternalArithmeticPrograms.addition (List.Vector.ofFn fun _ : Fin 2 =>
    evaluate InternalUnpair.right (List.Vector.ofFn ![value]))) + 1 = _
  rw [InternalArithmeticProgramsEvaluationProof.vectorTwo,
    InternalArithmeticProgramsEvaluationProof.exactAdditionEvaluation,
    InternalApplicationCertificateConstructorsEvaluationProof.rightEvaluation]
  simp [fuelValue, InternalApplicationValidityStack.payloadValue, two_mul]

theorem applicationFuelBound (d e fp ap : Nat) :
    1 + fuelValue (InternalApplicationValidityStack.functionValue d e fp) +
        fuelValue (InternalApplicationValidityStack.argumentValue d ap) + 1 ≤
      fuelValue (InternalApplicationValidityStack.applicationValue d e fp ap) := by
  have hb := InternalApplicationValidityStackStateProof.applicationPayloadBound
    (InternalApplicationValidityStack.applicationValue d e fp ap)
    (by simp [InternalApplicationValidityStack.tagValue, InternalApplicationValidityStack.payloadValue,
      InternalApplicationValidityStack.applicationValue])
  simp only [InternalApplicationValidityStack.functionPayloadValue,
    InternalApplicationValidityStack.argumentPayloadValue, InternalApplicationValidityStack.bodyValue,
    InternalApplicationValidityStack.payloadValue, InternalApplicationValidityStack.applicationValue,
    Nat.unpair_pair] at hb
  simp only [fuelValue, InternalApplicationValidityStack.payloadValue,
    InternalApplicationValidityStack.functionValue, InternalApplicationValidityStack.argumentValue,
    InternalApplicationValidityStack.applicationValue, Nat.unpair_pair]
  omega

theorem actualOriginalResultStackFuelBounds :
    InternalApplicationResultStackTargets.ActualOriginalResultStackFuelBounds := by
  constructor
  · intro value
    exact ⟨fuelEvaluation value, by simp [workWeightCons, visitWeight, workWeight]⟩
  · exact applicationFuelBound

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackStateProof
