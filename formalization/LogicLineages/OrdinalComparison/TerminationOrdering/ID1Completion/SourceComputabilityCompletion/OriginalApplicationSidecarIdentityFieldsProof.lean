module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityFieldsProof
open OriginalApplicationSidecar
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Reduce only a retained record projection, not the representative AST. -/
theorem originalSource (data : Data) (window : Program 1) :
    (originalData data window).oldSource = BottomParameter.normalized data.oldSource := rfl

theorem originalTarget (data : Data) (window : Program 1) :
    (originalData data window).oldTarget = BottomParameter.normalized data.oldTarget := rfl

theorem originalMember (data : Data) (window : Program 1) :
    (originalData data window).member =
      InternalOriginalUniformContextMembership.normalizedMember data.member := rfl

/-- Specialize the same field law to the once-refined original base. -/
theorem sameSource (data : Data) (window : Program 1) :
    (selectedData data window).oldSource = (originalData data window).oldSource :=
  (originalSource (baseData data window) window).trans (originalSource data window).symm

theorem sameTarget (data : Data) (window : Program 1) :
    (selectedData data window).oldTarget = (originalData data window).oldTarget :=
  (originalTarget (baseData data window) window).trans (originalTarget data window).symm

theorem sameMember (data : Data) (window : Program 1) :
    (selectedData data window).member = (originalData data window).member :=
  (originalMember (baseData data window) window).trans (originalMember data window).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityFieldsProof
