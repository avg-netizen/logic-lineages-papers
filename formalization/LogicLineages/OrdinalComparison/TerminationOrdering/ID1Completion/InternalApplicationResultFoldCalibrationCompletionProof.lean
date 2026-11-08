module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationExecutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationCompletionProof
open InternalApplicationResultStack InternalApplicationResultFoldCalibration
open InternalApplicationResultFoldCalibrationExecutionProof InternalApplicationResultFoldCalibrationMeaningProof
open InternalApplicationResultStackStateProof

theorem actualOriginalCompletedResultFold :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalCompletedResultFold := by
  intro guard leaf combine value results count hc
  have hw : workWeight [visitValue value] ≤ count := by
    simpa [workWeightCons, visitWeight, workWeight] using hc
  have ht := liveSufficientFuel guard leaf combine count
    (⟨1, [visitValue value], results⟩ : State) rfl hw
  apply terminalResult guard leaf combine _ _ ht
  rw [iterateMeaning]
  simp [stateMeaning, workMeaning, visitValue]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationCompletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationCompletionProof
