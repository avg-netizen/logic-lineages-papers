module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalProof
open UniformCertificateCompletion OriginalNeutralComputabilityGlobal OriginalNeutralComputabilityGlobalTargets

theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    Properties n arity p := by
  dsimp only [Properties]
  intro symbols S table hS
  exact ⟨OriginalApplicationComputabilityProof.actualOriginalFinalAcceptedOutputNonLambda
      n arity p hp symbols S table hS,
    OriginalApplicationComputabilityProof.actualOriginalFinalAcceptedApplicationComputable
      n arity p hp symbols S table hS,
    OriginalNeutralApplicationSuccessorProof.actualOriginalFinalApplicationSuccessorComputability
      n arity p hp symbols S table hS,
    OriginalNeutralTypeInductionProof.actualOriginalFinalNeutralComputabilityExpansion
      n arity p hp symbols S table hS,
    OriginalVariableComputabilityProof.actualOriginalFinalVariableComputability
      n arity p hp symbols S table hS⟩

/-- The previous selection is retained, not selected again for each type,
source context, Gamma or new certificate consumer. -/
theorem actualOriginalNeutralComputabilityGlobalSelection :
    ActualOriginalNeutralComputabilityGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,hcert⟩ :=
    OriginalChildCertificateGlobalProof.actualOriginalChildCertificateGlobalSelection n arity
  exact ⟨p,hp,hcert,properties n arity p hp.1⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalProof
