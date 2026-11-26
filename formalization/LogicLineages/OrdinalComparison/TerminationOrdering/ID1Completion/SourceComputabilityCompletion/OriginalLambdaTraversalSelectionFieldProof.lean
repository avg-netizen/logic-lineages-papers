module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Generic field laws keep the potentially large representative opaque. -/
theorem hereditaryWindow (q : GlobalSourcePackage.Inputs) :
    (OriginalHereditaryLambdaGlobal.finalInputs q).window = q.window := rfl
theorem hereditarySource (q : GlobalSourcePackage.Inputs) :
    (OriginalHereditaryLambdaGlobal.finalInputs q).base.oldSource = q.base.oldSource := rfl
theorem hereditaryTarget (q : GlobalSourcePackage.Inputs) :
    (OriginalHereditaryLambdaGlobal.finalInputs q).base.oldTarget = q.base.oldTarget := rfl
theorem hereditaryMember (q : GlobalSourcePackage.Inputs) :
    (OriginalHereditaryLambdaGlobal.finalInputs q).base.member = q.base.member := rfl

theorem dataEquality (a b : Data) (hs : a.oldSource = b.oldSource)
    (ht : a.oldTarget = b.oldTarget) (hr : a.oldRepresentative = b.oldRepresentative)
    (hm : a.member = b.member) : a = b := by
  cases a with
  | mk asrc atgt arep amem =>
    cases b with
    | mk bsrc btgt brep bmem =>
      dsimp only at hs ht hr hm
      cases hs
      cases ht
      cases hr
      cases hm
      rfl

theorem finalWindow (p : GlobalSourcePackage.Inputs) : (finalInputs p).window = p.window :=
  hereditaryWindow (prepareInputs p)

theorem finalBase (p : GlobalSourcePackage.Inputs) :
    (finalInputs p).base =
      { OriginalTransparentLambdaValidity.refineData p.base with
        oldRepresentative := (finalInputs p).base.oldRepresentative } := by
  apply dataEquality
  · exact hereditarySource (prepareInputs p)
  · exact hereditaryTarget (prepareInputs p)
  · rfl
  · exact hereditaryMember (prepareInputs p)

theorem finalIdentity (p : GlobalSourcePackage.Inputs) :
    finalData p = OriginalTransparentLambdaFinal.selectedData p.base
      (finalInputs p).base.oldRepresentative p.window :=
  congrArg₂ OuterSelection.data (finalBase p) (finalWindow p)

theorem leafSource (rawData : Data) (window : Program 1) :
    (leafData rawData window).oldSource =
      BottomParameter.normalized (transparentData rawData).oldSource :=
  (OriginalApplicationSidecarIdentityFieldsProof.sameSource (transparentData rawData) window).trans
    (OriginalApplicationSidecarIdentityFieldsProof.originalSource (transparentData rawData) window)

theorem leafTarget (rawData : Data) (window : Program 1) :
    (leafData rawData window).oldTarget =
      BottomParameter.normalized (transparentData rawData).oldTarget :=
  (OriginalApplicationSidecarIdentityFieldsProof.sameTarget (transparentData rawData) window).trans
    (OriginalApplicationSidecarIdentityFieldsProof.originalTarget (transparentData rawData) window)

theorem leafMember (rawData : Data) (window : Program 1) :
    (leafData rawData window).member =
      InternalOriginalUniformContextMembership.normalizedMember rawData.member :=
  (OriginalApplicationSidecarIdentityFieldsProof.sameMember (transparentData rawData) window).trans
    (OriginalApplicationSidecarIdentityFieldsProof.originalMember (transparentData rawData) window)

theorem sameSource (p : GlobalSourcePackage.Inputs) :
    (finalData p).oldSource = (leafData p.base p.window).oldSource := by
  rw [finalIdentity, leafSource]
  exact (OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
    p.base (finalInputs p).base.oldRepresentative p.window).1

theorem sameTarget (p : GlobalSourcePackage.Inputs) :
    (finalData p).oldTarget = (leafData p.base p.window).oldTarget := by
  rw [finalIdentity, leafTarget]
  exact (OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
    p.base (finalInputs p).base.oldRepresentative p.window).2.1

theorem sameMember (p : GlobalSourcePackage.Inputs) :
    (finalData p).member = (leafData p.base p.window).member := by
  rw [finalIdentity, leafMember]
  exact (OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
    p.base (finalInputs p).base.oldRepresentative p.window).2.2

theorem sameValidity (p : GlobalSourcePackage.Inputs) :
    InternalOriginalUniformDescentSelection.validity (finalData p) =
      InternalOriginalUniformDescentSelection.validity (leafData p.base p.window) :=
  OriginalApplicationSidecarIdentityProgramsProof.validityCongr
    (leafData p.base p.window) (finalData p) (sameSource p) (sameTarget p) (sameMember p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
