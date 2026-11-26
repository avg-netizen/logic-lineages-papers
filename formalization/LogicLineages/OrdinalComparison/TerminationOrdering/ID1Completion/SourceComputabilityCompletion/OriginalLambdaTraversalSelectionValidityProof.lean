module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open OriginalLambdaTraversalSelectionFieldProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The acyclic selected leaf and the generic final validity bridge have
identical source/target/member ASTs. The representative remains opaque. -/
theorem leafValidity (rawData : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity (leafData rawData window) =
      InternalOriginalUniformDescentSelection.validity
        (OriginalTransparentLambdaFinal.selectedData rawData rawData.oldRepresentative window) := by
  have hf := OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
    rawData rawData.oldRepresentative window
  exact OriginalApplicationSidecarIdentityProgramsProof.validityCongr _ _
    ((leafSource rawData window).trans hf.1.symm)
    ((leafTarget rawData window).trans hf.2.1.symm)
    ((leafMember rawData window).trans hf.2.2.symm)

theorem leafTargetValidity (rawData : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.targetValidity (leafData rawData window) =
      InternalOriginalUniformDescentSelection.targetValidity
        (OriginalTransparentLambdaFinal.selectedData rawData rawData.oldRepresentative window) := by
  have hf := OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
    rawData rawData.oldRepresentative window
  unfold InternalOriginalUniformDescentSelection.targetValidity
  rw [(leafTarget rawData window).trans hf.2.1.symm]

/-- Independent arithmetic laws for the actual selected leaf's validator,
not native evaluation or a C-invariant hypothesis. -/
theorem leafSourceCollapse (rawData : Data) (window : Program 1) :
    OriginalTransparentLambdaFinal.SourceCollapse rawData (leafData rawData window) := by
  intro positive alpha Delta out input parameter
  rw [leafValidity]
  exact OriginalTransparentLambdaFinalInternalProof.actualOriginalTransparentFinalSourceCollapse
    rawData rawData.oldRepresentative window positive alpha Delta out input parameter

theorem leafTargetCollapse (rawData : Data) (window : Program 1) :
    OriginalTransparentLambdaFinal.TargetCollapse rawData (leafData rawData window) := by
  intro positive alpha Delta out input parameter
  rw [leafTargetValidity]
  exact OriginalTransparentLambdaFinalLeafCollapseProof.actualOriginalTransparentFinalTargetCollapse
    rawData rawData.oldRepresentative window positive alpha Delta out input parameter

theorem leafSourceLambda (rawData : Data) (window : Program 1) :
    OriginalTransparentLambdaFinal.SourceLambdaLaw (leafData rawData window) :=
  OriginalTransparentLambdaFinalSourceLambdaProof.sourceLambdaLaw rawData (leafData rawData window)
    (leafSourceCollapse rawData window) (leafMember rawData window)

theorem leafTargetLambda (rawData : Data) (window : Program 1) :
    OriginalTransparentLambdaFinal.TargetLambdaLaw (leafData rawData window) :=
  OriginalTransparentLambdaFinalTargetLambdaProof.targetLambdaLaw rawData (leafData rawData window)
    (leafTargetCollapse rawData window)

/-- The same graph laws already hold at the actual final tuple, with no
canonical traversal premise. Its distinct representative is not unfolded. -/
theorem finalInternalLaws (p : GlobalSourcePackage.Inputs) :
    OriginalTransparentLambdaFinal.InternalLaws p.base (finalData p) := by
  rw [finalIdentity]
  exact OriginalTransparentLambdaFinalInternalProof.internalLaws
    p.base (finalInputs p).base.oldRepresentative p.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
