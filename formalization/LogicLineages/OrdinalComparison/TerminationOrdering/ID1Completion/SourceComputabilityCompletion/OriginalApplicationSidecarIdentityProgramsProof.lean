module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
open OriginalApplicationSidecar OriginalApplicationSidecarIdentityFieldsProof
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Congruence at the three literal inputs of the original validator. -/
theorem validityCongr (before after : Data)
    (hs : after.oldSource = before.oldSource)
    (ht : after.oldTarget = before.oldTarget)
    (hm : after.member = before.member) :
    InternalOriginalUniformDescentSelection.validity after =
      InternalOriginalUniformDescentSelection.validity before := by
  unfold InternalOriginalUniformDescentSelection.validity
  rw [hs, ht, hm]

/-- The root guard observes only the validator and membership Programs. -/
theorem rootGuardCongr (before after : Data)
    (hv : InternalOriginalUniformDescentSelection.validity after =
      InternalOriginalUniformDescentSelection.validity before)
    (hm : after.member = before.member) :
    InternalParameterizedCanonicalResultFold.rootGuard after =
      InternalParameterizedCanonicalResultFold.rootGuard before := by
  simp only [InternalParameterizedCanonicalResultFold.rootGuard,
    InternalParameterizedCanonicalResultFold.validity, hv, hm]

theorem sameValidity (data : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity (selectedData data window) =
      InternalOriginalUniformDescentSelection.validity (originalData data window) :=
  validityCongr (originalData data window) (selectedData data window)
    (sameSource data window) (sameTarget data window) (sameMember data window)

theorem sameRootGuard (data : Data) (window : Program 1) :
    InternalParameterizedCanonicalResultFold.rootGuard (selectedData data window) =
      InternalParameterizedCanonicalResultFold.rootGuard (originalData data window) :=
  rootGuardCongr (originalData data window) (selectedData data window)
    (sameValidity data window) (sameMember data window)

/-- Name the actual once-normalized validator without expanding its AST. -/
theorem originalValidity (data : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity (originalData data window) =
      InternalParameterizedApplicationValidityFold.sourceP
        (BottomParameter.normalized data.oldSource)
        (BottomParameter.normalized data.oldTarget)
        (InternalOriginalUniformContextMembership.normalizedMember data.member) := by
  unfold InternalOriginalUniformDescentSelection.validity
  rw [originalSource, originalTarget, originalMember]

/-- This is the existing guard's literal three-field normalization. -/
theorem activeNormalized (data : Data) (window : Program 1) :
    OriginalFunctionNeutrality.active data window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (InternalParameterizedApplicationValidityFold.sourceP
          (BottomParameter.normalized data.oldSource)
          (BottomParameter.normalized data.oldTarget)
          (InternalOriginalUniformContextMembership.normalizedMember data.member)) := rfl

theorem sameActive (data : Data) (window : Program 1) :
    OriginalFunctionNeutrality.active (baseData data window) window =
      OriginalFunctionNeutrality.active data window :=
  (activeNormalized (baseData data window) window).trans (activeNormalized data window).symm

theorem activeOriginal (data : Data) (window : Program 1) :
    OriginalFunctionNeutrality.active data window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (InternalOriginalUniformDescentSelection.validity (originalData data window)) := by
  rw [originalValidity]
  exact activeNormalized data window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
