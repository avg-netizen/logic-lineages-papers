module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableEndpointIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionProof
open UniformCertificateCompletion

/-- After neutral refinement the actual pipeline changes only the
representative and effective leaf. The original endpoint ignores both fields. -/
theorem hereditaryEndpoint (p : GlobalSourcePackage.Inputs) :
    OriginalHereditaryLambdaGlobal.endpoint p =
      InternalParameterizedStructuralEndpointGuard.selectedEndpoint
        (OuterSelection.data (OriginalHereditaryLambdaGlobal.finalInputs p).base
          (OriginalHereditaryLambdaGlobal.finalInputs p).window) := by
  exact (OriginalNeutralVariableProof.finalEndpoint
    (OriginalConstructorShape.refineInputs
      (OriginalFunctionNeutrality.refineInputs
        (OriginalApplicationSidecar.refineInputs p)))).symm

theorem actualFinalClosedLeafIdentity : ActualFinalClosedLeafIdentity := by
  intro p
  have h := (OriginalHereditaryLambdaGlobalPreparationProof.pipelineIdentities
    (OriginalLambdaTraversalSelection.prepareInputs p)).2.2
  rw [hereditaryEndpoint] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionProof
