module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
open UniformCertificateCompletion

/-- Neither original leaf refinement changes the endpoint. The representative
refinement changes only oldRepresentative; the endpoint's validity/member
fields do not inspect that field. This is equality of the literal ASTs. -/
theorem finalEndpoint (p : GlobalSourcePackage.Inputs) :
    OriginalNeutralLeaf.endpoint
      (OriginalVariableRepresentative.refineInputs (OriginalNeutralLeaf.refineInputs p)) =
      OriginalNeutralLeaf.endpoint p := by
  simp only [OriginalNeutralLeaf.endpoint,
    InternalParameterizedStructuralEndpointGuard.selectedEndpoint,
    InternalOriginalUniformDescentSelection.validity,
    InternalOriginalUniformDescentSelection.targetValidity,
    OuterSelection.data,SpineApplicationTargets.selectedData,
    BottomSource.selection,BottomRepresentative.readyData,
    InternalOriginalUniformContextMembership.normalizeData,
    BottomRepresentative.baseData,BottomParameter.baseData,SpineRepresentative.baseData,
    OriginalVariableRepresentative.refineInputs,OriginalConstructorLeaf.refineInputs,
    OriginalNeutralLeaf.refineInputs,OriginalVariableRepresentative.baseData]


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
