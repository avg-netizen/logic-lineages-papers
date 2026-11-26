module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalPreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalGlobalProof
open UniformCertificateCompletion OriginalTransparentLambdaFinal

/-- Reapply the ENTIRE accepted global Properties theorem at the refined
original input. The native theorem only supplies its calibration hypothesis;
the new internal laws were proved separately from literal Program graphs. -/
theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    Properties n arity p := by
  have hnative := OriginalTransparentLambdaFinalPreparationProof.nativeRefinement n arity p hp
  exact ⟨hnative,
    OriginalHereditaryLambdaGlobalProof.properties n arity (refineInputs p) hnative.1,
    OriginalTransparentLambdaFinalInternalProof.finalInternalLaws p⟩

/-- Select one original input before every window and Gamma. Its same final
tuple retains the complete previous Package while gaining two-way final
lambda validity. No canonical-body or computability claim is inferred. -/
theorem actualOriginalTransparentFinalGlobalSelection :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  exact ⟨p,hp,properties n arity p hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalGlobalProof
