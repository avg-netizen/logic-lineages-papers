module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceGlobalProof
open UniformCertificateCompletion OriginalFinalObjectCoherence

theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    Properties n arity p :=
  ⟨OriginalLambdaTraversalFinalGlobalProof.properties n arity p hp,
    OriginalFinalObjectCoherenceNativeProof.actualOriginalFinalObjectCanonicalCancellation n arity p hp,
    OriginalFinalObjectCoherenceNativeProof.actualOriginalFinalObjectRankInvariance n arity p hp⟩

/-- Extend the already-chosen global tuple with native consequences at that
same p; the entire previous package is retained verbatim. -/
theorem actualOriginalFinalObjectGlobalSelection :
    OriginalFinalObjectCoherenceTargets.ActualOriginalFinalObjectGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,hprevious⟩ :=
    OriginalLambdaTraversalFinalGlobalProof.actualOriginalLambdaTraversalGlobalSelection n arity
  exact ⟨p,hp,hprevious,
    OriginalFinalObjectCoherenceNativeProof.actualOriginalFinalObjectCanonicalCancellation n arity p hp,
    OriginalFinalObjectCoherenceNativeProof.actualOriginalFinalObjectRankInvariance n arity p hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceGlobalProof
