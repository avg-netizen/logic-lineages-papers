module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityValidatorProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaValidityRootProof
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem sourceCallback (data : Data) :
    (fun value parameter => evaluate (sourceRoot data) (List.Vector.ofFn ![value,parameter])) =
      sourceRootValue (binaryValue data.oldSource) (binaryValue data.member) := by
  funext value parameter
  exact sourceRootEvaluation data (List.Vector.ofFn ![value,parameter])

theorem targetCallback (data : Data) :
    (fun value parameter => evaluate (targetRoot data) (List.Vector.ofFn ![value,parameter])) =
      targetRootValue (binaryValue data.oldTarget) := by
  funext value parameter
  exact targetRootEvaluation data (List.Vector.ofFn ![value,parameter])

theorem oneCallback :
    (fun value parameter => evaluate (InternalLessThan.constantOne 2)
      (List.Vector.ofFn ![value,parameter])) = (fun _ _ : Nat => 1) := by
  funext value parameter
  rfl

theorem sourceValidatorEvaluation (rawData : Data) (v : List.Vector Nat 2) :
    evaluate (sourceValidator rawData) v =
      sourceValidatorValue rawData (v.get 0) (v.get 1) := by
  unfold sourceValidator sourceValidatorValue
  rw [OriginalHereditaryValidityEvaluationBoundedProof.validatorEvaluation,
    sourceCallback, targetCallback]
  rfl

theorem targetValidatorEvaluation (rawData : Data) (v : List.Vector Nat 2) :
    evaluate (targetValidator rawData) v =
      targetValidatorValue rawData (v.get 0) (v.get 1) := by
  unfold targetValidator targetValidatorValue
  rw [OriginalHereditaryValidityEvaluationBoundedProof.validatorEvaluation,
    targetCallback, oneCallback]

theorem actualOriginalTransparentValidatorCalibration :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentValidatorCalibration := by
  intro rawData v
  exact ⟨sourceValidatorEvaluation rawData v, targetValidatorEvaluation rawData v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityValidatorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityValidatorProof
