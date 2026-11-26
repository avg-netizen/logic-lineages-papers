module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateCodingProof
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep OriginalLambdaCertificate

theorem liftStepEncoding (child : StepCertificate) :
    liftStep (stepCertificateNumber child) = stepCertificateNumber (liftCertificate child) := by
  simp [liftStep,stepCertificateNumber,liftCertificate,pathNumber,
    NumberedMultisetNumeric.numbersNumber]

theorem stripLiftEncoding (child : StepCertificate) :
    stripStep (stepCertificateNumber (liftCertificate child)) = stepCertificateNumber child := by
  simp [stripStep,stepCertificateNumber,liftCertificate,pathNumber,
    NumberedMultisetNumeric.numbersNumber]

theorem actualLambdaCertificateStrip :
    OriginalLambdaCertificateTargets.ActualLambdaCertificateStrip := by
  refine ⟨?_,liftStepEncoding,?_⟩
  · intro certificate
    simp [stripStep]
  · intro certificate decoded rest hd hp
    have he := NumberedNumericStepSupportProof.certificateSound certificate decoded hd
    rcases decoded with ⟨path,replacement,root⟩
    dsimp at hp
    subst path
    have hs : stripStep certificate = stepCertificateNumber ⟨rest,replacement,root⟩ := by
      rw [← he]
      exact stripLiftEncoding ⟨rest,replacement,root⟩
    refine ⟨hs,?_,?_⟩
    · rw [hs]
      exact NumberedNumericStepSupportProof.certificateRoundTrip ⟨rest,replacement,root⟩
    · rw [hs,liftStepEncoding]
      exact he.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateCodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateCodingProof
