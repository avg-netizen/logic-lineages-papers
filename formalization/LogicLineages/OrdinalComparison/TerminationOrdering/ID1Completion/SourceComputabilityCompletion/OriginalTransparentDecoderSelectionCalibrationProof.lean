module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
open OriginalTransparentDecoderSelection UniformCertificateCompletion
open OriginalVariableLeavesRefinementProof

/-- The local M comes from p's SAME member. Native calibration of the two
transparent leaves transfers all original input calibration to q, then to the
single variable refinement, without changing any other input field. -/
theorem actualOriginalTransparentDecoderCalibration :
    OriginalTransparentDecoderSelectionTargets.ActualOriginalTransparentDecoderCalibration := by
  intro n arity p H G W hp hH hG hW
  have hM := OriginalUniverseDecoderGuardCalibrationProof.originalMemberCalibration
    n p.base.member hp.1.2.2.2
  have hs := OriginalUniverseDecoderSourceCalibrationProof.sourceCalibration
    n arity H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
      hH hG hM hW
  have ht := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration
    n arity H G hH hG
  have hq : GlobalSourcePackage.InputsCalibrated n arity (transparentInputs H G W p) :=
    ⟨⟨hs,ht,hp.1.2.2.1,hp.1.2.2.2⟩,hp.2⟩
  have hr := refinedInputsCalibration n arity G (transparentInputs H G W p) hG hq
  refine ⟨hq,hr,hM,?_⟩
  intro v
  have hv := actualOriginalVariableLeavesRefinementEquality n arity G
    (transparentInputs H G W p).base hG hq.1 v
  exact ⟨hs v,ht v,(hs v).trans (hp.1.1 v).symm,
    (ht v).trans (hp.1.2.1 v).symm,hv.1,hv.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
