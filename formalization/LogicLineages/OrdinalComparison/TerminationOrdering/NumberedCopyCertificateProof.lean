module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate

theorem typedCopyCheck : NumberedCopyCertificateTargets.ActualTypedCopyCheck := by
  intro n arity symbols S table Gamma g q r
  constructor
  · intro h
    obtain ⟨tau,q⟩ := q
    cases q with
    | var => simp [copyTarget] at h
    | lam => simp [copyTarget] at h
    | app => simp [copyTarget] at h
    | bottom => simp [copyTarget] at h
    | ordinary => simp [copyTarget] at h
    | numbered k f tau base types extras =>
      cases k with
      | zero => simp [copyTarget] at h
      | succ k =>
        simp only [copyTarget] at h
        split at h
        next hg =>
          obtain ⟨ht,habove,hwindow⟩ := hg
          cases ht
          cases h
          exact .copy k f base types extras habove hwindow
        next => contradiction
  · intro h
    cases h with
    | copy k f base types extras habove hwindow => simp [copyTarget,habove,hwindow]

theorem numericCopyCertificate : NumberedCopyCertificateTargets.ActualNumericCopyCertificate := by
  intro n arity symbols S Gamma table source target
  constructor
  · rintro ⟨certificate,h⟩
    cases hd : decodeUniverse n arity symbols S Gamma source with
    | none => simp [copyCertificateTest,hd] at h
    | some q =>
      cases hg : decodeHeadNumber n certificate with
      | none => simp [copyCertificateTest,hd,hg] at h
      | some code =>
        cases ht : copyTarget arity symbols S table Gamma (decodeHead code) q with
        | none => simp [copyCertificateTest,hd,hg,ht] at h
        | some r =>
          have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mp hd
          exact ⟨decodeHead code,q,r,hq.2,(typedCopyCheck n arity symbols S table Gamma (decodeHead code) q r).mp ht,hq.1,
            by simpa [copyCertificateTest,hd,hg,ht] using h⟩
  · rintro ⟨g,q,r,hq,hcopy,hsource,htarget⟩
    have hd := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mpr ⟨hsource,hq⟩
    have hg : decodeHeadNumber n (headNumber (headCode g))=some (headCode g) :=
      NumberedNumericDecodingSupportProof.headNumericRoundTrip (headCode g)
    have ht := (typedCopyCheck n arity symbols S table Gamma g q r).mpr hcopy
    refine ⟨headNumber (headCode g),?_⟩
    simp [copyCertificateTest,hd,hg,NumberedAuxiliaryDecodingProof.headRoundTrip,ht,htarget]

theorem numericCopySound : NumberedCopyCertificateTargets.ActualNumericCopySound := by
  intro n arity symbols S hc Gamma table source target certificate h
  obtain ⟨g,q,r,hq,hcopy,hsource,htarget⟩ :=
    (numericCopyCertificate n arity symbols S Gamma table source target).mp ⟨certificate,h⟩
  cases hcopy with
  | copy k f base types extras habove hwindow =>
    have hs := WindowStep.copy (symbols := symbols) (S := S) k f g base types extras habove hwindow
    exact ⟨headResult g,_,_,hq,NumberedWindowReductionProof.stepGood symbols S hc hs hq,hs,hsource,htarget⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateProof
