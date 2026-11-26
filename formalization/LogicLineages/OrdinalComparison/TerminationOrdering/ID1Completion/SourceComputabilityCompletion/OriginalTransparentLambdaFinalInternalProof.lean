module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalInternalProof
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalLeafCollapseProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalTransparentFinalSourceCollapse :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalSourceCollapse := by
  intro rawData representative window
  exact OriginalTransparentLambdaFinalConjunctionProof.sourceCollapse rawData
    (selectedData rawData representative window)
    (actualOriginalTransparentFinalTargetCollapse rawData representative window)
    (actualOriginalTransparentFinalUniverseCollapse rawData representative window)

/-- The root membership callback is exactly the final selected member,
not the member of an earlier representative preparation. -/
theorem actualOriginalTransparentFinalSourceLambda :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalSourceLambda := by
  intro rawData representative window
  exact OriginalTransparentLambdaFinalSourceLambdaProof.sourceLambdaLaw rawData
    (selectedData rawData representative window)
    (actualOriginalTransparentFinalSourceCollapse rawData representative window)
    (OriginalTransparentLambdaFinalSelectionProof.actualOriginalTransparentFinalSelectionFields
      rawData representative window).2.2

theorem actualOriginalTransparentFinalTargetLambda :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalTargetLambda := by
  intro rawData representative window
  exact OriginalTransparentLambdaFinalTargetLambdaProof.targetLambdaLaw rawData
    (selectedData rawData representative window)
    (actualOriginalTransparentFinalTargetCollapse rawData representative window)

theorem internalLaws (rawData : Data) (representative : Program 2) (window : Program 1) :
    InternalLaws rawData (selectedData rawData representative window) :=
  ⟨⟨actualOriginalTransparentFinalTargetCollapse rawData representative window,
      actualOriginalTransparentFinalUniverseCollapse rawData representative window,
      actualOriginalTransparentFinalSourceCollapse rawData representative window⟩,
    actualOriginalTransparentFinalSourceLambda rawData representative window,
    actualOriginalTransparentFinalTargetLambda rawData representative window⟩

/-- Specialize only by literal complete-Data identity. All derivations still
refer to the same actual final source/target Programs of the retained tuple. -/
theorem finalInternalLaws (p : GlobalSourcePackage.Inputs) :
    InternalLaws p.base (finalData p) := by
  rw [(OriginalTransparentLambdaFinalSelectionProof.pipelineIdentity p).1]
  exact internalLaws p.base (finalInputs p).base.oldRepresentative (finalInputs p).window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalInternalProof
