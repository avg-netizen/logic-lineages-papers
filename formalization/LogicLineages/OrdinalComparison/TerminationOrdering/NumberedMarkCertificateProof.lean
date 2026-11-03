module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedMarkCertificate

theorem typedMarkCheck : NumberedMarkCertificateTargets.ActualTypedMarkCheck := by
  intro n arity Gamma q r
  constructor
  · rintro ⟨label,h⟩
    simp only [markTarget,Option.map_eq_some_iff] at h
    obtain ⟨b,hb,rfl⟩ := h
    exact .mk label q.2 b hb
  · intro h
    cases h with
    | mk label q r he => exact ⟨label,by simp [markTarget,he]⟩

theorem lambdaMarkCheck : NumberedMarkCertificateTargets.ActualLambdaMarkCheck := by
  intro n arity Gamma sigma tau label q r
  simp [markTarget,finiteMark,Option.map_eq_some_iff]

theorem numericMarkCertificate : NumberedMarkCertificateTargets.ActualNumericMarkCertificate := by
  intro n arity symbols S Gamma source target
  constructor
  · rintro ⟨label,h⟩
    cases hd : decodeUniverse n arity symbols S Gamma source with
    | none => simp [markCertificateTest,hd] at h
    | some q =>
      cases hm : markTarget label q with
      | none => simp [markCertificateTest,hd,hm] at h
      | some r =>
        have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mp hd
        exact ⟨q,r,hq.2,(typedMarkCheck n arity Gamma q r).mp ⟨label,hm⟩,hq.1,
          by simpa [markCertificateTest,hd,hm] using h⟩
  · rintro ⟨q,r,hq,hm,hs,ht⟩
    have hd := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source q).mpr ⟨hs,hq⟩
    obtain ⟨label,he⟩ := (typedMarkCheck n arity Gamma q r).mpr hm
    exact ⟨label,by simp [markCertificateTest,hd,he,ht]⟩

theorem numericMarkSound : NumberedMarkCertificateTargets.ActualNumericMarkSound := by
  intro n arity symbols S Gamma above source target label h
  cases hd : decodeUniverse n arity symbols S Gamma source with
  | none => simp [markCertificateTest,hd] at h
  | some q =>
    obtain ⟨tau,q⟩ := q
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma source ⟨tau,q⟩).mp hd
    cases hm : finiteMark label q with
    | none => simp [markCertificateTest,hd,markTarget,hm] at h
    | some r =>
      have hr : InUniverse symbols S r :=
        NumberedUniverseBindingProof.markGood (fun t => t∈S) (HeadInWindow arity symbols S) label q r hm hq.2
      have hs := NumberedWindowOccurrenceProof.finiteMarkStep (Fin n) arity symbols S above label Gamma tau q r hm
      exact ⟨tau,q,r,hq.2,hr,hm,hs,hq.1,by simpa [markCertificateTest,hd,markTarget,hm] using h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateProof
