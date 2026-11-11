module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateCodingProof
open NumberedStepCertificate NumberedNumericStep OriginalBetaResult

theorem actualOriginalBetaCertificateCoding :
    OriginalBetaResultTargets.ActualOriginalBetaCertificateCoding := by
  intro replacement
  have he : rootCertificate replacement =
      stepCertificateNumber ⟨[],replacement,Nat.pair 2 0⟩ := by
    rfl
  refine ⟨he,?_⟩
  rw [he]
  exact NumberedNumericStepSupportProof.certificateRoundTrip ⟨[],replacement,Nat.pair 2 0⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateCodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateCodingProof
