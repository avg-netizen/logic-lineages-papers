module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityStandardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityGlobalProof
open UniformCertificateCompletion OriginalFinalNativeAccessibility
open OriginalFinalNativeAccessibilityCanonicalProof OriginalFinalNativeAccessibilityStandardProof

/-- Preserve the entire previous SAME-final tuple, and append unconditional
native consequences. The retained Package is explicitly at finalInputs p. -/
theorem actualOriginalFinalNativeProperties :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalFinalNativeProperties := by
  intro n arity p hp
  exact ⟨OriginalFinalObjectCoherenceGlobalProof.properties n arity p hp,
    finalPackage n arity p hp,
    actualOriginalCanonicalCarrierAccessibility n arity,
    actualOriginalContextObjectAccessibility n arity,
    actualOriginalFinalStandardLeastMembership n arity p hp,
    actualOriginalFinalClosedFormulaTruth n arity p hp⟩

/-- Select p BEFORE all finite windows and runtime contexts. No caller rank,
scalar, calibration or all-term premise is introduced. This is standard-model
truth only and does not assert the still-pending internal ID1 derivation. -/
theorem actualOriginalFinalNativeGlobalSelection :
    OriginalFinalNativeAccessibilityTargets.ActualOriginalFinalNativeGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,hprevious⟩ :=
    OriginalFinalObjectCoherenceGlobalProof.actualOriginalFinalObjectGlobalSelection n arity
  exact ⟨p,hp,hprevious,finalPackage n arity p hp,
    actualOriginalCanonicalCarrierAccessibility n arity,
    actualOriginalContextObjectAccessibility n arity,
    actualOriginalFinalStandardLeastMembership n arity p hp,
    actualOriginalFinalClosedFormulaTruth n arity p hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityGlobalProof
