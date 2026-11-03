module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetCertificate NumberedMultisetNumeric NumberedMulCertificate NumberedDirectCertificate NumberedSelectCertificate NumberedRootDecomposition NumberedNumericRoot

theorem rootSelectorRoundTrip : NumberedNumericRootTargets.ActualRootSelectorRoundTrip := by
  intro n arity Gamma selector
  cases selector with
  | direct rule => cases rule <;> simp [selectorNumber,decodeSelector]
  | select types index =>
    have ht : decodeTypes (typesNumber types)=some types := NumberedNumericDecodingSupportProof.typesRoundTrip types
    simp [selectorNumber,decodeSelector,ht]
  | copy head =>
    have hh : decodeHeadNumber n (headNumber (headCode head))=some (headCode head) := NumberedNumericDecodingSupportProof.headNumericRoundTrip (headCode head)
    simp [selectorNumber,decodeSelector,hh,NumberedAuxiliaryDecodingProof.headRoundTrip]
  | mul certificate =>
    have hc : decodeCertificate n arity Gamma (certificateNumber certificate)=some certificate := NumberedMultisetNumericProof.multisetCertificateRoundTrip n arity Gamma certificate
    simp [selectorNumber,decodeSelector,hc]

theorem typedRootSelectors : NumberedNumericRootTargets.ActualTypedRootSelectors := by
  intro n arity symbols S Gamma table q r
  constructor
  · rintro ⟨selector,h⟩
    cases selector with
    | direct rule =>
      have he : directTarget arity Gamma rule q=some r := by simpa [selectorTest] using h
      exact .direct rule q r ((NumberedDirectCertificateProof.directRuleCheck n arity Gamma rule q r).mp he)
    | select types index =>
      have he : selectTarget arity Gamma types index q=some r := by simpa [selectorTest] using h
      exact .select q r ((NumberedSelectCertificateProof.selectCertificates n arity Gamma q r).mp ⟨types,index,he⟩)
    | copy head =>
      have he : copyTarget arity symbols S table Gamma head q=some r := by simpa [selectorTest] using h
      have hc := (NumberedCopyCertificateProof.typedCopyCheck n arity symbols S table Gamma head q r).mp he
      cases hc with
      | copy k f base types extras habove hwindow => exact .copy k f head base types extras habove hwindow
    | mul certificate =>
      exact .mul q r ((NumberedMulCertificateProof.typedMulCertificates n arity symbols S Gamma q r).mp ⟨certificate,h⟩)
  · intro h
    cases h with
    | direct rule q r hi =>
      have he := (NumberedDirectCertificateProof.directRuleCheck n arity Gamma rule q r).mpr hi
      exact ⟨.direct rule,by simp [selectorTest,he]⟩
    | select q r hi =>
      obtain ⟨types,index,he⟩ := (NumberedSelectCertificateProof.selectCertificates n arity Gamma q r).mpr hi
      exact ⟨.select types index,by simp [selectorTest,he]⟩
    | mul q r hi =>
      obtain ⟨certificate,he⟩ := (NumberedMulCertificateProof.typedMulCertificates n arity symbols S Gamma q r).mpr hi
      exact ⟨.mul certificate,he⟩
    | copy k f g base types extras habove hwindow =>
      have he := (NumberedCopyCertificateProof.typedCopyCheck n arity symbols S table Gamma g _ _).mpr (.copy k f base types extras habove hwindow)
      exact ⟨.copy g,by simp [selectorTest,he]⟩

theorem numericRootCertificates : NumberedNumericRootTargets.ActualNumericRootCertificates := by
  intro n arity symbols S Gamma table source target
  constructor
  · rintro ⟨certificate,h⟩
    cases hq : decodeUniverse n arity symbols S Gamma source with
    | none => simp [numericRootTest,hq] at h
    | some q =>
      cases hr : decodePackedNumber n arity Gamma target with
      | none => simp [numericRootTest,hq,hr] at h
      | some r =>
        cases hc : decodeSelector n arity Gamma certificate with
        | none => simp [numericRootTest,hq,hr,hc] at h
        | some selector =>
          have ht : selectorTest n arity symbols S Gamma table q r selector=true := by simpa [numericRootTest,hq,hr,hc] using h
          have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mp hq
          exact ⟨q,r,hsource.2,(typedRootSelectors n arity symbols S Gamma table q r).mp ⟨selector,ht⟩,
            hsource.1,NumberedNumericDecodingProof.packedNumericSound n arity Gamma target r hr⟩
  · rintro ⟨q,r,hgood,hm,hs,ht⟩
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mpr ⟨hs,hgood⟩
    have hr : decodePackedNumber n arity Gamma target=some r := by
      rw [←ht]
      exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r
    obtain ⟨selector,hc⟩ := (typedRootSelectors n arity symbols S Gamma table q r).mpr hm
    have hd : decodeSelector n arity Gamma (selectorNumber selector)=some selector := rootSelectorRoundTrip n arity Gamma selector
    exact ⟨selectorNumber selector,by simp [numericRootTest,hq,hr,hd,hc]⟩

theorem numericRootSound : NumberedNumericRootTargets.ActualNumericRootSound := by
  intro n arity symbols S hc Gamma table source target certificate h
  obtain ⟨q,r,hq,hm,hs,ht⟩ := (numericRootCertificates n arity symbols S Gamma table source target).mp ⟨certificate,h⟩
  obtain ⟨tau,a,b,rfl,rfl,hstep⟩ := NumberedRootDecompositionProof.rootErasure hm
  exact ⟨tau,a,b,hq,NumberedWindowReductionProof.stepGood symbols S hc hstep hq,hstep,hs,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootProof
