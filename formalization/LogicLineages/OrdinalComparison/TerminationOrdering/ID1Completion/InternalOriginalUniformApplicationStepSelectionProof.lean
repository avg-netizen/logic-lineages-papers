module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
open Source InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformApplicationStepSelectionTargets
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalParameterizedStructuralEndpointGuard (selectedEndpoint)

theorem actualOriginalUniformStepLeafProgram : ActualOriginalUniformStepLeafProgram :=
  InternalOriginalUniformApplicationStepSelectionEvaluationProof.actualOriginalUniformStepLeafProgram

/-- The same globally selected old-step leaf receives the actual selected
endpoint. Calibration preserves every original input, while the internal
application-step equation remains symbolic and has no calibration premise. -/
theorem actualOriginalUniformApplicationStepSelection :
    ActualOriginalUniformApplicationStepSelection := by
  intro n arity data hc
  obtain ⟨oldStep,hleaf,hslices⟩ := actualOriginalUniformStepLeafProgram n arity
  refine ⟨oldStep,hleaf,?_,?_⟩
  · intro symbols S Gamma table
    exact InternalParameterizedApplicationStepCheckerProof.actualParameterizedOriginalCheckerCalibration
      n arity symbols S Gamma table (selectedEndpoint data) oldStep
      (parameterCode symbols S Gamma table)
      (InternalParameterizedStructuralEndpointGuardProof.actualOriginalParameterizedStructuralEndpointCalibration
        n arity data hc symbols S Gamma table)
      (hslices symbols S Gamma table)
  · intro body α Delta d e arrow s t a certificate sourceApp targetApp lifted out parameter
    exact InternalParameterizedApplicationStepCheckerProof.actualParameterizedOriginalLiftedChecker
      body (selectedEndpoint data) oldStep α Delta d e arrow s t a certificate
      sourceApp targetApp lifted out parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
