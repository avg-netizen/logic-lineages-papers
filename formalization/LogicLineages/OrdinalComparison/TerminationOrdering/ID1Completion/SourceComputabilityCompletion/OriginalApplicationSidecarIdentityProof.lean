module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof
open OriginalApplicationSidecar UniformCertificateCompletion
open OriginalApplicationSidecarIdentityFieldsProof OriginalApplicationSidecarIdentityProgramsProof

/-- Assemble the unchanged frozen conjunction from literal field laws and
Program congruence. Specialize the existing final-input theorems directly. -/
theorem actualOriginalApplicationSidecarSelectionIdentity :
    OriginalApplicationSidecarTargets.ActualOriginalApplicationSidecarSelectionIdentity := by
  constructor
  · intro data window
    exact ⟨originalSource data window, originalTarget data window, originalMember data window,
      sameSource data window, sameTarget data window, sameMember data window,
      sameValidity data window, sameRootGuard data window,
      sameActive data window, activeOriginal data window⟩
  · intro p
    exact ⟨OriginalFunctionNeutralityInputProof.finalWindow (refineInputs p),
      OriginalFunctionNeutralityInputProof.finalSelectedData (refineInputs p)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof.actualOriginalApplicationSidecarSelectionIdentity
