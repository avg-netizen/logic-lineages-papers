module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateProof
open OrdinaryArithmeticQuotient RankedPrecedenceCertificate RankedPrecedenceCompleteness NumericPrecedenceCertificate

theorem actualNumericRankCalibration : NumericPrecedenceCertificateTargets.ActualNumericRankCalibration := by
  intro n context certificate
  unfold numericRankTest
  cases hc : (Encodable.decode (α := Context n) context) <;>
    cases hr : decodeRank n certificate <;>
    simp [hc,hr]
  exact RankedPrecedenceCertificateProof.actualRankCertificateTest n _ _

theorem rankDecoderPrimitive (n : Nat) : Primrec (decodeRank n) := by
  apply OrdinaryArithmeticQuotientDecoderProof.finiteCanonicalDecoder
  exact OrdinaryArithmeticQuotientDecoderProof.canonicalFinPi n _
    (fun _ => OrdinaryArithmeticQuotientDecoderProof.canonicalFin n)

theorem actualNumericRankPrimitive : NumericPrecedenceCertificateTargets.ActualNumericRankPrimitive := by
  intro n
  have ht : Primrec (fun p : (Fin n → Fin n → Bool) × (Fin n → Fin n) => rankCertificateTest p.1 p.2) :=
    Primrec.dom_finite _
  have hi : Primrec (fun p : Context n × Nat => (decodeRank n p.2).any (fun rank => rankCertificateTest p.1.2 rank)) :=
    QuotientDirectPrimrecSupportProof.optionAnyPrimitive ((rankDecoderPrimitive n).comp Primrec.snd)
      (ht.comp ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂
  exact (QuotientDirectPrimrecSupportProof.optionAnyPrimitive
    ((OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp Primrec.fst)
    (hi.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂).to₂

theorem actualNumericRankExistence : NumericPrecedenceCertificateTargets.ActualNumericRankExistence := by
  intro n context
  constructor
  · rintro ⟨certificate,h⟩
    obtain ⟨ctx,rank,hc,hr,hcert⟩ := (actualNumericRankCalibration n context certificate).mp h
    exact ⟨ctx,hc,(RankedPrecedenceCompletenessProof.actualRankCertificateExistence n ctx.2).mp
      ⟨rank,(RankedPrecedenceCertificateProof.actualRankCertificateTest n ctx.2 rank).mpr hcert⟩⟩
  · rintro ⟨ctx,hc,ht⟩
    obtain ⟨rank,hr⟩ := (RankedPrecedenceCompletenessProof.actualRankCertificateExistence n ctx.2).mpr ht
    refine ⟨@Encodable.encode _ (rankEncoding n) rank,(actualNumericRankCalibration n context _).mpr ?_⟩
    refine ⟨ctx,rank,hc,?_,(RankedPrecedenceCertificateProof.actualRankCertificateTest n ctx.2 rank).mp hr⟩
    exact @Encodable.encodek _ (rankEncoding n) rank

end LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateProof
