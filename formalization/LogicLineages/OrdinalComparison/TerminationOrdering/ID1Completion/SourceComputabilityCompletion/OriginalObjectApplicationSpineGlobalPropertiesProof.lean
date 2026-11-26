module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalPropertiesProof
open UniformCertificateCompletion OriginalObjectApplicationSpineGlobal

/-- Every calibrated original input tuple supplies the entire frozen
per-tuple conjunction. The same final inputs serve all finite source windows,
the original Object applications and the complete earlier Package. -/
theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    FinalProperties n arity p := by
  let r := OriginalApplicationSidecar.finalInputs p
  have hside := OriginalApplicationComponentCoherenceGlobalInputProof.refinedInputsCalibrated
    n arity p hp
  refine ⟨OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity p hp,
    OriginalFunctionNeutralityFinalPackageProof.finalPackage n arity
      (OriginalApplicationSidecar.refineInputs p) hside,
    OriginalFunctionNeutralityFinalFieldsProof.finalRootFields (OriginalApplicationSidecar.refineInputs p),
    OriginalFunctionNeutralityFinalFieldsProof.finalMarkPreservation (OriginalApplicationSidecar.refineInputs p),
    OriginalFullFoldSpineProof.actualOriginalFinalFullFoldSpinePreservation p,
    OriginalFunctionNeutralityFinalFieldsProof.finalNeutralBottom (OriginalApplicationSidecar.refineInputs p),
    OriginalApplicationComponentCoherenceFinalProof.finalPairedComponents p,
    OriginalNeutralQuotientProof.actualOriginalNeutralQuotientEdgeElimination p,
    OriginalNeutralApplicationEdgeProof.actualOriginalNeutralApplicationEdgeElimination p,
    OriginalNonLambdaApplicationEdgeProof.actualOriginalNonLambdaApplicationEdgeElimination p,
    OriginalNonLambdaApplicationPathProof.actualOriginalNonLambdaApplicationPositivePathElimination p,?_⟩
  intro symbols S table hS
  exact ⟨OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
      n arity p hp symbols S table hS,
    OriginalSourceNeutralApplicationPathProof.actualOriginalSourceNeutralApplicationPositivePathElimination
      n arity p hp symbols S table hS,
    OriginalSourceApplicationReconstructionProof.actualOriginalSourceApplicationReconstruction
      (OuterSelection.data r.base r.window) r.window r.oldComp r.oldVertex r.oldResult
      (OrdinaryArithmeticQuotient.contextCode symbols S table),
    OriginalSourceNeutralApplicationObjectPathProof.actualOriginalSourceNeutralApplicationObjectPositivePathElimination
      n arity p hp symbols S table hS,
    OriginalFunctionNeutralityFinalVariablesProof.finalVariableLaws
      n arity (OriginalApplicationSidecar.refineInputs p) hside symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalPropertiesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalPropertiesProof
