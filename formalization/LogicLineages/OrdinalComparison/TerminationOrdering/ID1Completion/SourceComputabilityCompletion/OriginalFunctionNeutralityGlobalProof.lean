module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalPackageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalVariablesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityGlobalProof
open UniformCertificateCompletion

/-- Select one original tuple, then refine it in the fixed order. Every law
below concerns the exact same final source, computability package and lift. -/
theorem actualOriginalFunctionNeutralityGlobalSelection :
    OriginalFunctionNeutralityTargets.ActualOriginalFunctionNeutralityGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  refine ⟨p,hp,?_,?_,?_,?_,?_,?_⟩
  · exact OriginalFunctionNeutralityInputProof.finalInputsCalibrated n arity p hp
  · exact OriginalFunctionNeutralityFinalPackageProof.finalPackage n arity p hp
  · exact OriginalFunctionNeutralityFinalFieldsProof.finalRootFields p
  · exact OriginalFunctionNeutralityFinalFieldsProof.finalMarkPreservation p
  · exact OriginalFunctionNeutralityFinalFieldsProof.finalNeutralBottom p
  · intro symbols S table hS
    exact OriginalFunctionNeutralityFinalVariablesProof.finalVariableLaws
      n arity p hp symbols S table hS

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityGlobalProof
