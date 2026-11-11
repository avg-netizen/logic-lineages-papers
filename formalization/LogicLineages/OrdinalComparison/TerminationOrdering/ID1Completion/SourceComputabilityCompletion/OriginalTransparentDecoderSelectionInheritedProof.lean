module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalCancellationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRankProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCancellationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionInheritedProof
open OriginalTransparentDecoderSelection UniformCertificateCompletion
open OriginalVariableLeavesInternalProof OriginalVariableLeavesRefinementProof
open OriginalFinalVariableWeakeningProof
open OriginalFinalVariableCanonicalFixednessProof OriginalFinalVariableCanonicalCancellationProof
open OriginalFinalVariableCanonicalRankProof
open OriginalFinalVariableObjectCalibrationProof OriginalFinalVariableObjectExposureProof
open OriginalFinalVariableObjectFixednessProof OriginalFinalVariableObjectCancellationProof
open OriginalFinalVariableObjectRankProof

/-- Rebuild the complete previous conjunction for ARBITRARY calibrated q.
No existential variable/canonical/Object selection is invoked: every field
belongs to this SAME q and its SAME once-refined final pipeline. -/
theorem actualOriginalTransparentDecoderInheritedProperties :
    OriginalTransparentDecoderSelectionTargets.ActualOriginalTransparentDecoderInheritedProperties := by
  intro n arity q G hq hG
  have hr := refinedInputsCalibration n arity G q hG hq
  have hn := OriginalFinalNativeAccessibilityGlobalProof.actualOriginalFinalNativeProperties
    n arity (OriginalVariableLeaves.refineInputs G q) hr
  have hw : OriginalFinalVariableWeakening.Properties n arity q G :=
    ⟨hq,hG,hr,hn,actualOriginalVariableLeavesInternalBranches G q.base,
      actualOriginalVariableLeavesRefinementEquality n arity G q.base hG hq.1,
      actualOriginalFinalVariableSourceWeakening G q,
      actualOriginalFinalVariableTargetWeakening G q⟩
  have hc : OriginalFinalVariableCanonical.Properties n arity q G :=
    ⟨hw,hn,actualOriginalFinalVariableFixedness G q,
      actualOriginalFinalVariableCancellation G q,
      actualOriginalFinalVariableRankPreservation G q⟩
  have ho : OriginalFinalVariableObject.Properties n arity q G :=
    ⟨hc,hn,
      actualOriginalFinalVariableObjectCalibration (OriginalVariableLeaves.refineInputs G q),
      actualOriginalFinalVariableObjectExposure (OriginalVariableLeaves.refineInputs G q),
      actualOriginalFinalVariableObjectFixedness G q,
      actualOriginalFinalVariableObjectCancellation G q,
      actualOriginalFinalVariableObjectRankPreservation G q⟩
  exact ⟨ho,hn.2.1⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionInheritedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionInheritedProof
