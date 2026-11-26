module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalCoherenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGlobalProof
open UniformCertificateCompletion OriginalLambdaTraversalSelection

/-- Retain the ENTIRE previous hereditary/global package at the actual
prepared tuple. Native preparation supplies calibration only; every internal
final law is independently proved and instantiated at the identical Data. -/
theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    Properties n arity p := by
  have prepared := OriginalLambdaTraversalNativePreparationProof.actualOriginalLambdaTraversalNativePreparation
    n arity p hp
  exact ⟨prepared,
    OriginalHereditaryLambdaGlobalProof.properties n arity (prepareInputs p) prepared.1,
    OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws p,
    OriginalLambdaTraversalFinalTransitionProof.actualOriginalLambdaTraversalFinalTransition p,
    OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical p,
    OriginalLambdaTraversalFinalCoherenceProof.actualOriginalLambdaTraversalFinalBodyFixed p,
    OriginalLambdaTraversalFinalCoherenceProof.actualOriginalLambdaTraversalFinalLambdaEquation p⟩

/-- Choose ONE original globally calibrated tuple before every finite
window and runtime context. The complete retained Package and all four
new exact final coherence laws coexist at that actual final tuple. -/
theorem actualOriginalLambdaTraversalGlobalSelection :
    OriginalLambdaTraversalSelectionTargets.ActualOriginalLambdaTraversalGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  exact ⟨p,hp,properties n arity p hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGlobalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGlobalProof.actualOriginalLambdaTraversalGlobalSelection
