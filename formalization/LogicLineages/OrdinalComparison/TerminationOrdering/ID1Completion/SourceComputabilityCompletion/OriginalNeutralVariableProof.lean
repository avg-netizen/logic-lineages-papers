module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableEndpointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
open UniformCertificateCompletion

/-- One input tuple precedes both refinements and every window. The final
source, computability and lift are shared by the full Package, original
neutral-leaf law, variable certificate inversion and variable leastness. -/
theorem actualOriginalNeutralVariableGlobalSelection :
    OriginalNeutralVariableTargets.ActualOriginalNeutralVariableGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  let q := OriginalNeutralLeaf.refineInputs p
  let r := OriginalVariableRepresentative.refineInputs q
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    OriginalNeutralLeafProof.refinedInputsCalibrated n arity p hp
  have hr : GlobalSourcePackage.InputsCalibrated n arity r := variableInputsCalibrated n arity q hq
  refine ⟨p,hp,hq,hr,?_,finalNeutralLaw p,?_⟩
  · exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction n arity r hr).2.2
  · intro symbols S table hS
    exact ⟨OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom
        n arity q hq symbols S table hS,
      OriginalVariableObjectLeastProof.actualOriginalVariableObjectLeast
        n arity q hq symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
