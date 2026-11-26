module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesGlobalProof
open OriginalVariableLeaves UniformCertificateCompletion
open OriginalVariableLeavesContextGuardProof OriginalVariableLeavesInternalProof
open OriginalVariableLeavesRefinementProof

/-- Refine the chosen INITIAL tuple before any source window or runtime Gamma.
The old representative/member and all other input fields stay literal. Every
prior property applies to this very tuple through the unchanged final pipeline. -/
theorem actualOriginalVariableLeavesGlobalSelection :
    OriginalVariableLeavesTargets.ActualOriginalVariableLeavesGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  obtain ⟨guard,hg⟩ := actualOriginalVariableContextGuardSelection n
  have hq := refinedInputsCalibration n arity guard p hg hp
  exact ⟨p,guard,hp,hg,hq,
    OriginalFinalNativeAccessibilityGlobalProof.actualOriginalFinalNativeProperties n arity
      (refineInputs guard p) hq,
    actualOriginalVariableLeavesInternalBranches guard p.base,
    actualOriginalVariableLeavesRefinementEquality n arity guard p.base hg hp.1⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesGlobalProof
