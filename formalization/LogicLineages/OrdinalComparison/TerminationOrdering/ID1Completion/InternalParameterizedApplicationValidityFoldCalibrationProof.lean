module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldCalibrationProof
open Source InternalApplicationValidityStack InternalParameterizedApplicationValidityFold
open InternalOriginalStepGuard InternalParameterizedApplicationResultFoldCalibration
open InternalParameterizedApplicationResultFoldCalibrationProof
open InternalApplicationValidityStackStateProof InternalApplicationValidityStackInvariantProof
open InternalApplicationValidityCalibrationProof InternalApplicationValidityStackEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem nodeAtPEvaluation (node : Program 2) (d e f a p : Nat) :
    evaluate (nodeAtP node) (List.Vector.ofFn ![d,e,f,a,p]) =
      evaluate node (List.Vector.ofFn ![e,p]) := rfl

 theorem combinePEvaluation (node : Program 2) (d e f a p : Nat) :
    evaluate (combineP node) (List.Vector.ofFn ![d,e,f,a,p]) =
      if evaluate node (List.Vector.ofFn ![e,p]) = 1 ∧ f = 1 ∧ a = 1 then 1 else 0 := by
  rw [combineP, actualConjunctionEvaluation, actualConjunctionEvaluation, nodeAtPEvaluation]
  change (if evaluate node (List.Vector.ofFn ![e,p]) = 1 ∧
    (if f = 1 ∧ a = 1 then 1 else 0) = 1 then 1 else 0) = _
  by_cases hf : f = 1 <;> by_cases ha : a = 1 <;> simp [hf, ha]

 theorem validatorSemanticEvaluation (node oldLeaf : Program 2) (value parameter : Nat) :
    evaluate (validatorP node oldLeaf) (List.Vector.ofFn ![value,parameter]) =
      semanticFoldP openingGuardP (leafP oldLeaf) (combineP node) value parameter :=
  (actualOriginalParameterizedBoundedResultFoldCalibration
    openingGuardP (leafP oldLeaf) (combineP node) value parameter).2

 theorem actualOriginalParameterizedValidityFoldRecurrence :
    InternalParameterizedApplicationValidityFoldTargets.ActualOriginalParameterizedValidityFoldRecurrence := by
  intro node oldLeaf value parameter
  have he := actualOriginalParameterizedSemanticResultFoldEquation
    openingGuardP (leafP oldLeaf) (combineP node) value parameter
  simp only [← validatorSemanticEvaluation] at he
  rw [combinePEvaluation] at he
  simpa only [openingGuardP, oneEvaluation, and_true, leafP, evalNormalize] using he

/-- Strong induction is on the ORIGINAL packed input payload. The callback
calibration is required only at the one fixed parameter used throughout. -/
 theorem validatorNormalizedCalibrationP (node oldLeaf : Program 2)
    (nodeValue valid : Nat → Nat) (parameter : Nat)
    (hn : ∀ value, evaluate node (List.Vector.ofFn ![value,parameter]) = nodeValue value)
    (hl : ∀ value, evaluate oldLeaf (List.Vector.ofFn ![value,parameter]) = valid value)
    (hb : ∀ value, (if valid value = 1 then 1 else 0) = valid value)
    (app : ∀ value, tagValue value = 2 →
      (valid value = 1 ↔ nodeValue (resultTypeValue value) = 1 ∧
        valid (functionChildValue value) = 1 ∧ valid (argumentChildValue value) = 1))
    (value : Nat) :
    evaluate (validatorP node oldLeaf) (List.Vector.ofFn ![value,parameter]) = valid value := by
  have main : ∀ k value, payloadValue value = k →
      evaluate (validatorP node oldLeaf) (List.Vector.ofFn ![value,parameter]) = valid value := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro value hk
      rw [actualOriginalParameterizedValidityFoldRecurrence]
      by_cases ht : tagValue value = 2
      · have hbound := applicationPayloadBound value ht
        have hf : payloadValue (functionChildValue value) < k := by
          rw [functionChildPayload]
          omega
        have ha : payloadValue (argumentChildValue value) < k := by
          rw [argumentChildPayload]
          omega
        rw [if_pos ht, hn,
          ih _ hf _ rfl, ih _ ha _ rfl]
        simpa only [← app value ht] using hb value
      · rw [if_neg ht, hl]
        exact hb value
  exact main (payloadValue value) value rfl

 theorem actualOriginalParameterizedValidityFoldCalibration :
    InternalParameterizedApplicationValidityFoldTargets.ActualOriginalParameterizedValidityFoldCalibration := by
  intro n arity symbols S Gamma oldSource oldTarget member parameter hs ht hm
  have targetCalibration : ∀ value,
      evaluate (targetP oldTarget) (List.Vector.ofFn ![value,parameter]) =
        targetValidityValue n arity Gamma value := by
    intro value
    exact validatorNormalizedCalibrationP (InternalLessThan.constantOne 2) oldTarget
      (fun _ => 1) (targetValidityValue n arity Gamma) parameter
      (fun _ => oneEvaluation _) ht (fun _ => boolNormalized _)
      (targetAppAcceptance n arity Gamma) value
  have universeCalibration : ∀ value,
      evaluate (universeP oldSource member) (List.Vector.ofFn ![value,parameter]) =
        sourceValidityValue n arity symbols S Gamma value := by
    intro value
    exact validatorNormalizedCalibrationP member oldSource
      (InternalStructuralEndpointGuard.membershipValue S)
      (sourceValidityValue n arity symbols S Gamma) parameter hm hs
      (fun _ => boolNormalized _) (sourceAppAcceptance n arity symbols S Gamma) value
  intro value
  refine ⟨targetCalibration value, universeCalibration value, ?_⟩
  rw [sourceP, actualConjunctionEvaluation, targetCalibration, universeCalibration]
  have he : (targetValidityValue n arity Gamma value = 1 ∧
      sourceValidityValue n arity symbols S Gamma value = 1) ↔
      sourceValidityValue n arity symbols S Gamma value = 1 :=
    ⟨And.right, fun h => ⟨originalSourceImpliesTarget n arity symbols S Gamma value h, h⟩⟩
  simp only [he]
  exact boolNormalized _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldCalibrationProof
