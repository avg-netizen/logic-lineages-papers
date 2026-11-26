module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalVariablesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityProof
open Source UniformCertificateCompletion OriginalVariableComputabilityTargets

theorem actualOriginalFinalVariableComputability : ActualOriginalFinalVariableComputability := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  have hside := OriginalApplicationComponentCoherenceGlobalInputProof.refinedInputsCalibrated
    n arity q hq
  have hbottom := (OriginalFunctionNeutralityFinalVariablesProof.finalVariableLaws n arity
    (OriginalApplicationSidecar.refineInputs q) hside symbols S table hS).1
  exact OriginalVariableComputabilityCoreProof.variableComputable n arity r hr symbols S table hS
    hbottom (OriginalNeutralTypeInductionProof.actualOriginalFinalNeutralComputabilityExpansion
      n arity p hp symbols S table hS)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityProof
