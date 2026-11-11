module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportProof
open UniformCertificateCompletion
open OriginalTransparentDecoderFinalTransportTargets
open OriginalTransparentDecoderFinalTransportTransferProof
open OriginalTransparentDecoderFinalTransportTargetProof
open OriginalTransparentDecoderFinalTransportSourceProof
open OriginalTransparentDecoderValidatorCollapseProof

theorem actualOriginalTransparentDecoderFinalTargetWeakening :
    ActualOriginalTransparentDecoderFinalTargetWeakening := by
  intro p H G W
  exact weakeningOfGraphEquality _ _
    (actualOriginalTransparentDecoderFinalTargetCollapse p H G W)
    (targetWeakening H G)

theorem actualOriginalTransparentDecoderFinalTargetErasure :
    ActualOriginalTransparentDecoderFinalTargetErasure := by
  intro p H G W
  exact erasureOfGraphEquality _ _
    (actualOriginalTransparentDecoderFinalTargetCollapse p H G W)
    (targetErasure H G)

theorem actualOriginalTransparentDecoderFinalSourceWeakening :
    ActualOriginalTransparentDecoderFinalSourceWeakening := by
  intro p H G W
  exact weakeningOfGraphEquality _ _
    (actualOriginalTransparentDecoderFinalSourceCollapse p H G W)
    (sourceWeakening H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W)

theorem actualOriginalTransparentDecoderFinalSourceErasure :
    ActualOriginalTransparentDecoderFinalSourceErasure := by
  intro p H G W
  exact erasureOfGraphEquality _ _
    (actualOriginalTransparentDecoderFinalSourceCollapse p H G W)
    (sourceErasure H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportProof
