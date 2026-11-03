module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetNumeric NumberedTypedFocus NumberedStepCertificate NumberedNumericStep

theorem pathNumericRoundTrip : NumberedNumericStepTargets.ActualPathNumericRoundTrip := NumberedNumericStepSupportProof.pathRoundTrip
theorem pathNumericSound : NumberedNumericStepTargets.ActualPathNumericSound := NumberedNumericStepSupportProof.pathSound
theorem stepCertificateNumericRoundTrip : NumberedNumericStepTargets.ActualStepCertificateNumericRoundTrip := NumberedNumericStepSupportProof.certificateRoundTrip
theorem stepCertificateNumericSound : NumberedNumericStepTargets.ActualStepCertificateNumericSound := NumberedNumericStepSupportProof.certificateSound

theorem numericStepCertificates : NumberedNumericStepTargets.ActualNumericStepCertificates := by
  intro n arity symbols S Gamma table source target
  constructor
  · rintro ⟨certificate,h⟩
    cases hq : decodeUniverse n arity symbols S Gamma source with
    | none => simp [numericStepTest,hq] at h
    | some q =>
      obtain ⟨tau,q⟩ := q
      cases hr : decodePackedNumber n arity Gamma target with
      | none => simp [numericStepTest,hq,hr] at h
      | some r =>
        obtain ⟨sigma,r⟩ := r
        cases hc : decodeStepCertificate certificate with
        | none => simp [numericStepTest,hq,hr,hc] at h
        | some c =>
          simp only [numericStepTest,hq,hr,hc] at h
          split at h
          next ht =>
            cases ht
            have hs : stepTest n arity symbols S Gamma table q r c=true := by simpa using h
            have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source ⟨tau,q⟩).mp hq
            exact ⟨tau,q,r,hsource.2,NumberedStepCertificateProof.stepCertificateSound n arity symbols S Gamma table tau q r c hs,
              hsource.1,NumberedNumericDecodingProof.packedNumericSound n arity Gamma target ⟨tau,r⟩ hr⟩
          next => contradiction
  · rintro ⟨tau,q,r,hgood,hstep,hs,ht⟩
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source ⟨tau,q⟩).mpr ⟨hs,hgood⟩
    have hr : decodePackedNumber n arity Gamma target=some ⟨tau,r⟩ := by
      rw [←ht]
      exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma ⟨tau,r⟩
    obtain ⟨c,hc⟩ := NumberedStepCertificateProof.stepCertificateComplete n arity symbols S Gamma table tau q r hstep
    have hd : decodeStepCertificate (stepCertificateNumber c)=some c := stepCertificateNumericRoundTrip c
    exact ⟨stepCertificateNumber c,by simp [numericStepTest,hq,hr,hd,hc]⟩

theorem numericStepSound : NumberedNumericStepTargets.ActualNumericStepSound := by
  intro n arity symbols S hc Gamma table source target certificate h
  obtain ⟨tau,q,r,hq,hstep,hs,ht⟩ := (numericStepCertificates n arity symbols S Gamma table source target).mp ⟨certificate,h⟩
  exact ⟨tau,q,r,hq,NumberedWindowReductionProof.stepGood symbols S hc hstep hq,hstep,hs,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
