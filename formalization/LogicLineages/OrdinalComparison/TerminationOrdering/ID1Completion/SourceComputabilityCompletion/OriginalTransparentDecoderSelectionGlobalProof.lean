module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionInheritedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderHeadSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderWindowSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionGlobalProof
open OriginalTransparentDecoderSelection UniformCertificateCompletion
open OriginalTransparentDecoderSelectionFieldProof OriginalTransparentDecoderSelectionCalibrationProof
open OriginalTransparentDecoderSelectionInheritedProof

/-- Select the ORIGINAL p exactly once, then H, G and W exactly once. The
source's M is definitionally derived from that p.member. All inherited laws
are reconstructed for q, not borrowed from a separately selected tuple. -/
theorem actualOriginalTransparentDecoderSelection :
    OriginalTransparentDecoderSelectionTargets.ActualOriginalTransparentDecoderSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  obtain ⟨H,hH⟩ := OriginalTypedDecoderHeadSelectionProof.actualOriginalTypedHeadSelection n arity
  obtain ⟨G,hG⟩ := OriginalVariableLeavesContextGuardProof.actualOriginalVariableContextGuardSelection n
  obtain ⟨W,hW⟩ := OriginalUniverseDecoderWindowSelectionProof.actualOriginalUniverseWindowSelection n arity
  have hcal := actualOriginalTransparentDecoderCalibration n arity p H G W hp hH hG hW
  have hsource := OriginalUniverseDecoderSourceCalibrationProof.actualOriginalUniverseSourceCalibration
    n arity H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
      hH hG hcal.2.2.1 hW
  exact ⟨p,H,G,W,hp,hH,hG,hW,
    actualOriginalTransparentDecoderLiteralFields p H G W,hcal,
    actualOriginalTransparentDecoderInheritedProperties n arity (transparentInputs H G W p) G hcal.1 hG,
    hsource.2,OriginalTypedDecoderInternalProof.actualOriginalTypedInternalStep H⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionGlobalProof
