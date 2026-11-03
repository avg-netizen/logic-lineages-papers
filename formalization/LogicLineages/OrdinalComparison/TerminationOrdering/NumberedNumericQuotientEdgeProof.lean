module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedNumericStep NumberedQuotientPaths NumberedNumericQuotientEdge

theorem numericQuotientEdge : NumberedNumericQuotientEdgeTargets.ActualNumericQuotientEdge := by
  intro n arity symbols S Gamma table x y
  constructor
  · rintro ⟨certificate,h⟩
    let source := (Nat.unpair certificate).1
    let target := (Nat.unpair (Nat.unpair certificate).2).1
    let step := (Nat.unpair (Nat.unpair certificate).2).2
    cases hq : decodeUniverse n arity symbols S Gamma source with
    | none =>
      simp only [source] at hq
      simp [numericEdgeTest,hq] at h
    | some q =>
      cases hr : decodePackedNumber n arity Gamma target with
      | none =>
        simp only [source] at hq
        simp only [target] at hr
        simp [numericEdgeTest,hq,hr] at h
      | some r =>
        have hh : numericStepTest n arity symbols S Gamma table source target step=true ∧
            representativeCode symbols S q=x ∧ representativeCode symbols S r=y := by
          simpa [numericEdgeTest,source,target,step,hq,hr] using h
        obtain ⟨tau,a,b,hgood,hstep,ha,hb⟩ := (NumberedNumericStepProof.numericStepCertificates n arity symbols S Gamma table source target).mp ⟨step,hh.1⟩
        have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mp hq
        have htarget := NumberedNumericDecodingProof.packedNumericSound n arity Gamma target r hr
        have heq : (⟨tau,a⟩ : Packed (Fin n) arity Gamma)=q := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma (ha.trans hsource.1.symm)
        have her : (⟨tau,b⟩ : Packed (Fin n) arity Gamma)=r := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma (hb.trans htarget.symm)
        refine ⟨tau,a,b,hgood,hstep,?_,?_⟩
        · rw [heq]; exact hh.2.1
        · rw [her]; exact hh.2.2
  · rintro ⟨tau,q,r,hq,hstep,hx,hy⟩
    have hdq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) ⟨tau,q⟩).mpr ⟨rfl,hq⟩
    have hdr : decodePackedNumber n arity Gamma (packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma))=some ⟨tau,r⟩ := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma ⟨tau,r⟩
    obtain ⟨step,hs⟩ := (NumberedNumericStepProof.numericStepCertificates n arity symbols S Gamma table
      (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) (packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma))).mpr ⟨tau,q,r,hq,hstep,rfl,rfl⟩
    refine ⟨edgeCertificateNumber (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) (packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)) step,?_⟩
    simp [numericEdgeTest,edgeCertificateNumber,hdq,hdr,hs,hx,hy]

theorem numericEdgeCarrier : NumberedNumericQuotientEdgeTargets.ActualNumericEdgeCarrier := by
  intro n arity symbols S hc Gamma table x y certificate h
  obtain ⟨tau,q,r,hq,hstep,hx,hy⟩ := (numericQuotientEdge n arity symbols S Gamma table x y).mp ⟨certificate,h⟩
  exact ⟨(NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity symbols S hc Gamma x).mpr ⟨⟨tau,q⟩,hq,hx⟩,
    (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity symbols S hc Gamma y).mpr ⟨⟨tau,r⟩,NumberedWindowReductionProof.stepGood symbols S hc hstep hq,hy⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeProof
