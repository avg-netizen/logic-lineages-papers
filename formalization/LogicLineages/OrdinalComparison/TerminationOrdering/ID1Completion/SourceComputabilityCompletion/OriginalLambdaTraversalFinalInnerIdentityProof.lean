module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalSelectionFieldProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem innerSource (rawData : Data) (window : Program 1) :
    (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldSource =
      (leafData rawData window).oldSource := by
  rw [OriginalApplicationSidecarIdentityFieldsProof.originalSource, leafSource]
  rfl

theorem innerTarget (rawData : Data) (window : Program 1) :
    (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldTarget =
      (leafData rawData window).oldTarget := by
  rw [OriginalApplicationSidecarIdentityFieldsProof.originalTarget, leafTarget]
  rfl

theorem innerMember (rawData : Data) (window : Program 1) :
    (OriginalApplicationSidecar.originalData (preparedData rawData window) window).member =
      (leafData rawData window).member := by
  rw [OriginalApplicationSidecarIdentityFieldsProof.originalMember, leafMember]
  rfl

/-- Congruence uses only three retained record fields; the large guarded
representative is not unfolded or compared. -/
theorem innerValidity (rawData : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity
      (OriginalApplicationSidecar.originalData (preparedData rawData window) window) =
    InternalOriginalUniformDescentSelection.validity (leafData rawData window) :=
  OriginalApplicationSidecarIdentityProgramsProof.validityCongr _ _
    (innerSource rawData window) (innerTarget rawData window) (innerMember rawData window)

theorem selectedValidity (rawData : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity
      (OriginalApplicationSidecar.selectedData (preparedData rawData window) window) =
    InternalOriginalUniformDescentSelection.validity (leafData rawData window) :=
  (OriginalApplicationSidecarIdentityProgramsProof.sameValidity (preparedData rawData window) window).trans
    (innerValidity rawData window)

theorem innerSourcePremises {alpha : Type} (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha) :
    InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalApplicationSidecar.originalData (preparedData rawData window) window) input typ parameter =
    InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) input typ parameter := by
  simp only [InternalParameterizedCanonicalResultFold.sourcePremises,
    InternalParameterizedCanonicalResultFold.validity, innerValidity]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerIdentityProof
