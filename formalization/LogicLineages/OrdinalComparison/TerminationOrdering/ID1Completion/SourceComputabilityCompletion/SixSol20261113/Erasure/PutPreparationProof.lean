module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutPreparationProof
open PutIntegration

theorem actualPutPreparation : ActualPutPreparation := by
  intro n arity p H G W P hp hH hG hW hP
  have hc := OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
    n arity p H G W hp hH hG hW
  have hput := SixSol20261112.Erasure.PutRootCalibrationProof.actualOriginalPutCalibration
    n arity (OriginalTransparentDecoderSelection.transparentInputs H G W p) hc.1
  exact OriginalMixedPreparedProof.actualRetention n arity (seed p H G W) H G W P
    hput hH hG hW hP
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutPreparationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutPreparationProof
