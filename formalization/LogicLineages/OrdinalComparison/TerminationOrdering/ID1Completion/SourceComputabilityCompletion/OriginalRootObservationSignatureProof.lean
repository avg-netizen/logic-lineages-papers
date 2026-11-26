module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureProof
/-- Only specializes the arbitrary-observer theorem under the exact explicit
all-context calibration hypothesis. It supplies neither R nor a final tuple. -/
theorem actualSignatureCalibration : OriginalRootObservationTargets.SignatureCalibration := by
  intro R n arity symbols S c hR Gamma q
  rw [OriginalRootObservationNativeProof.nativeCalibration R n arity Gamma c q]
  exact OriginalRootObservationSignatureSupportProof.nativeSignature R symbols S c hR q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureProof
