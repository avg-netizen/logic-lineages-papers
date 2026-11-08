module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationExecutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
open Source InternalApplicationValidityStack InternalApplicationValidityCalibration InternalOriginalStepGuard
open InternalApplicationValidityCalibrationExecutionProof InternalApplicationValidityStackInvariantProof
open InternalApplicationValidityStackEvaluationProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem stateIterateInvariant (node valid : Nat → Nat)
    (app : ∀ value : Nat, tagValue value = 2 →
      (valid value = 1 ↔ node (resultTypeValue value) = 1 ∧
        valid (functionChildValue value) = 1 ∧ valid (argumentChildValue value) = 1))
    (count : Nat) (state : State) :
    stateValid valid (stateIterate node valid count state) ↔ stateValid valid state := by
  induction count with
  | zero => exact Iff.rfl
  | succ count ih =>
    exact (stepInvariant node valid app (stateIterate node valid count state)).trans ih

 theorem terminalValidity (valid : Nat → Nat) (state : State) (ht : terminal state) :
    (state.status = 1 ∧ state.work = []) ↔ stateValid valid state := by
  rcases ht with rfl | rfl <;> simp [stateValid, failedState]

 theorem validatorNormalizedCalibration (node leaf : Program 1) (nodeValue valid : Nat → Nat)
    (hn : ∀ value : Nat, evaluate node (List.Vector.ofFn ![value]) = nodeValue value)
    (hl : ∀ value : Nat, evaluate leaf (List.Vector.ofFn ![value]) = valid value)
    (app : ∀ value : Nat, tagValue value = 2 →
      (valid value = 1 ↔ nodeValue (resultTypeValue value) = 1 ∧
        valid (functionChildValue value) = 1 ∧ valid (argumentChildValue value) = 1))
    (v : List.Vector Nat 1) :
    evaluate (validator node leaf) v = if valid (v.get 0) = 1 then 1 else 0 := by
  rw [validator, unaryEvaluation, runEvaluation, finishedEncodedEvaluation]
  have hnf : (fun value => evaluate node (List.Vector.ofFn ![value])) = nodeValue := funext hn
  have hlf : (fun value => evaluate leaf (List.Vector.ofFn ![value])) = valid := funext hl
  rw [hnf, hlf]
  have ht : terminal (stateIterate nodeValue valid (payloadValue (v.get 0) + 1)
      (⟨1, [v.get 0]⟩ : State)) :=
    liveSufficientFuel nodeValue valid (payloadValue (v.get 0) + 1) _ rfl
      (by simp [workWeight])
  have he : ((stateIterate nodeValue valid (payloadValue (v.get 0) + 1)
        (⟨1, [v.get 0]⟩ : State)).status = 1 ∧
      (stateIterate nodeValue valid (payloadValue (v.get 0) + 1)
        (⟨1, [v.get 0]⟩ : State)).work = []) ↔ valid (v.get 0) = 1 := by
    have hh := (terminalValidity valid _ ht).trans
      (stateIterateInvariant nodeValue valid app (payloadValue (v.get 0) + 1)
        (⟨1, [v.get 0]⟩ : State))
    simpa [stateValid] using hh
  simp only [he]

 theorem boolNormalized (b : Bool) : (if b.toNat = 1 then 1 else 0) = b.toNat := by
  cases b <;> rfl

 theorem actualOriginalBoundedValidatorCalibration :
    InternalApplicationValidityCalibrationTargets.ActualOriginalBoundedValidatorCalibration := by
  intro n arity symbols S Gamma old member hc hm
  constructor
  · intro v
    rw [validatorNormalizedCalibration (InternalLessThan.constantOne 1) old.targetValid
      (fun _ => 1) (targetValidityValue n arity Gamma)
      (fun value => oneEvaluation _) (fun value => by simpa using hc.2 (List.Vector.ofFn ![value]))
      (targetAppAcceptance n arity Gamma)]
    exact boolNormalized _
  · intro v
    rw [validatorNormalizedCalibration member old.sourceValid
      (InternalStructuralEndpointGuard.membershipValue S)
      (sourceValidityValue n arity symbols S Gamma)
      (fun value => by simpa using hm (List.Vector.ofFn ![value]))
      (fun value => by simpa using hc.1 (List.Vector.ofFn ![value]))
      (sourceAppAcceptance n arity symbols S Gamma)]
    exact boolNormalized _

 theorem originalSourceImpliesTarget (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    targetValidityValue n arity Gamma value = 1 := by
  cases hd : NumberedNumericDecoding.decodePackedNumber n arity Gamma value with
  | none =>
    simp [sourceValidityValue, NumberedNumericCarrier.rawCarrierTest,
      NumberedNumericCarrier.decodeUniverse, hd] at hs
  | some q => simp [targetValidityValue, hd]

 theorem actualOriginalRecursiveValidityCalibration :
    InternalApplicationValidityCalibrationTargets.ActualOriginalRecursiveValidityCalibration := by
  intro n arity symbols S Gamma old member hc hm
  obtain ⟨ht, hs⟩ := actualOriginalBoundedValidatorCalibration n arity symbols S Gamma old member hc hm
  constructor
  · intro v
    change evaluate (InternalAcceptance.conjunction
      (validator (InternalLessThan.constantOne 1) old.targetValid)
      (validator member old.sourceValid)) v = _
    rw [actualConjunctionEvaluation, ht, hs]
    have he : (targetValidityValue n arity Gamma (v.get 0) = 1 ∧
        sourceValidityValue n arity symbols S Gamma (v.get 0) = 1) ↔
        sourceValidityValue n arity symbols S Gamma (v.get 0) = 1 :=
      ⟨And.right, fun h => ⟨originalSourceImpliesTarget n arity symbols S Gamma (v.get 0) h, h⟩⟩
    simp only [he]
    exact boolNormalized _
  · exact ht

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
