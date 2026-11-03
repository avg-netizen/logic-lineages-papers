module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetCertificate NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem naturalListRoundTrip : NumberedMultisetNumericTargets.ActualNaturalListRoundTrip := numbersRoundTrip
theorem naturalListDecodeSound : NumberedMultisetNumericTargets.ActualNaturalListDecodeSound := numbersSound
theorem packedListRoundTrip : NumberedMultisetNumericTargets.ActualPackedListRoundTrip := packedRoundTrip
theorem packedListDecodeSound : NumberedMultisetNumericTargets.ActualPackedListDecodeSound := packedSound

theorem multisetCertificateRoundTrip : NumberedMultisetNumericTargets.ActualMultisetCertificateRoundTrip := by
  intro n arity Gamma c
  cases c
  simp [decodeCertificate,certificateNumber,packedRoundTrip,numbersRoundTrip,List.map_map,Function.comp_def]

theorem multisetCertificateDecodeSound : NumberedMultisetNumericTargets.ActualMultisetCertificateDecodeSound := by
  intro n arity Gamma value c h
  cases hk : decodePackedList n arity Gamma (Nat.unpair value).1 with
  | none => simp [decodeCertificate,hk] at h
  | some kept =>
    cases hr : decodePackedList n arity Gamma (Nat.unpair (Nat.unpair value).2).1 with
    | none => simp [decodeCertificate,hk,hr] at h
    | some removed =>
      cases hi : decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1 with
      | none => simp [decodeCertificate,hk,hr,hi] at h
      | some inserted =>
        cases hw : decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2 with
        | none => simp [decodeCertificate,hk,hr,hi,hw] at h
        | some witnesses =>
          simp only [decodeCertificate,hk,hr,hi,hw,Option.bind_some,Option.some.injEq] at h
          cases h
          have hkept := packedSound n arity Gamma _ kept hk
          have hremoved := packedSound n arity Gamma _ removed hr
          have hinserted := packedSound n arity Gamma _ inserted hi
          have hwitnesses := numbersSound _ witnesses hw
          simp [certificateNumber,hkept,hremoved,hinserted,List.map_map,Function.comp_def,hwitnesses]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericProof
