module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionFieldProof
open OriginalTransparentDecoderSelection

/-- Both replacements are literal record updates. Variable leaves are refined
once; every other field is exactly the original field of the original p. -/
theorem actualOriginalTransparentDecoderLiteralFields :
    OriginalTransparentDecoderSelectionTargets.ActualOriginalTransparentDecoderLiteralFields := by
  intro p H G W
  exact ⟨rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionFieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionFieldProof
