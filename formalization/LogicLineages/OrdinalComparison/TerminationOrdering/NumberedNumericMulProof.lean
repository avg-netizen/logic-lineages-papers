module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedMultisetNumeric NumberedMulCertificate NumberedNumericMul

theorem numericMulCertificates : NumberedNumericMulTargets.ActualNumericMulCertificates := by
  intro n arity symbols S Gamma source target
  constructor
  · rintro ⟨certificate,h⟩
    cases hq : decodeUniverse n arity symbols S Gamma source with
    | none => simp [numericMulTest,hq] at h
    | some q =>
      cases hr : decodePackedNumber n arity Gamma target with
      | none => simp [numericMulTest,hq,hr] at h
      | some r =>
        cases hc : decodeCertificate n arity Gamma certificate with
        | none => simp [numericMulTest,hq,hr,hc] at h
        | some c =>
          have ht : mulCertificateTest n arity symbols S Gamma q r c=true := by simpa [numericMulTest,hq,hr,hc] using h
          have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mp hq
          exact ⟨q,r,hsource.2,(NumberedMulCertificateProof.typedMulCertificates n arity symbols S Gamma q r).mp ⟨c,ht⟩,
            hsource.1,NumberedNumericDecodingProof.packedNumericSound n arity Gamma target r hr⟩
  · rintro ⟨q,r,hgood,hm,hs,ht⟩
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mpr ⟨hs,hgood⟩
    have hr : decodePackedNumber n arity Gamma target=some r := by
      rw [←ht]
      exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r
    obtain ⟨c,hc⟩ := (NumberedMulCertificateProof.typedMulCertificates n arity symbols S Gamma q r).mpr hm
    have hd : decodeCertificate n arity Gamma (certificateNumber c)=some c :=
      NumberedMultisetNumericProof.multisetCertificateRoundTrip n arity Gamma c
    exact ⟨certificateNumber c,by simp [numericMulTest,hq,hr,hd,hc]⟩

theorem numericMulSound : NumberedNumericMulTargets.ActualNumericMulSound := by
  intro n arity symbols S Gamma above source target certificate h
  obtain ⟨q,r,hq,hm,hs,ht⟩ := (numericMulCertificates n arity symbols S Gamma source target).mp ⟨certificate,h⟩
  obtain ⟨c,hc⟩ := (NumberedMulCertificateProof.typedMulCertificates n arity symbols S Gamma q r).mpr hm
  obtain ⟨hr,tau,a,b,rfl,rfl,hstep⟩ := NumberedMulCertificateProof.typedMulSound n arity symbols S Gamma above q r c hc hq
  exact ⟨tau,a,b,hq,hr,hstep,hs,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulProof
