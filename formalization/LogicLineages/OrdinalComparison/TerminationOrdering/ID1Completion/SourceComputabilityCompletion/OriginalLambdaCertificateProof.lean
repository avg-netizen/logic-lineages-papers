module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateCodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep NumberedNumericDecoding NumberedNumericCarrier
open OriginalLambdaCertificate

/-- Open the original numeric acceptance in place. Source, target and
certificate are decoded exactly once, and the certificate itself determines
the accepted child. No existential completeness result is used. -/
theorem actualNumericLambdaCertificateNonbottomInversion :
    OriginalLambdaCertificateTargets.ActualNumericLambdaCertificateNonbottomInversion := by
  intro n arity symbols S Gamma table sigma tau body target certificate hn h
  cases hq : decodeUniverse n arity symbols S Gamma
      (packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma)) with
  | none => simp [numericStepTest,hq] at h
  | some q =>
    have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma)) q).mp hq
    have he : q = (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma) :=
      NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hsource.1
    subst q
    have hbody : InUniverse symbols S body := ⟨hsource.2.1.2.2,hsource.2.2⟩
    refine ⟨hbody,?_⟩
    cases hr : decodePackedNumber n arity Gamma target with
    | none => simp [numericStepTest,hq,hr] at h
    | some r =>
      obtain ⟨rho,r⟩ := r
      cases hc : decodeStepCertificate certificate with
      | none => simp [numericStepTest,hq,hr,hc] at h
      | some c =>
        simp only [numericStepTest,hq,hr,hc] at h
        split at h
        next ht =>
          cases ht
          have htarget : packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma) = target :=
            NumberedNumericDecodingProof.packedNumericSound n arity Gamma target ⟨.arrow sigma tau,r⟩ hr
          have hnonbottom : r ≠ .bottom (.arrow sigma tau) := by
            intro he
            subst r
            exact hn htarget.symm
          obtain ⟨body',rest,hresult,hpath,hchild⟩ :=
            OriginalLambdaCertificateTypedProof.actualTypedLambdaCertificateNonbottomInversion
              n arity symbols S Gamma table sigma tau body r c hnonbottom h
          subst r
          obtain ⟨hstrip,hdecode,hrestore⟩ :=
            OriginalLambdaCertificateCodingProof.actualLambdaCertificateStrip.2.2
              certificate c rest hc hpath
          refine ⟨body',c,rest,rfl,hpath,htarget.symm,hstrip,hdecode,hrestore,hchild,?_⟩
          have hdbody := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S
            (sigma :: Gamma) (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
            ⟨tau,body⟩).mpr ⟨rfl,hbody⟩
          have hdbody' := NumberedNumericDecodingProof.packedNumericRoundTrip n arity (sigma :: Gamma)
            (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma))
          simpa [numericStepTest,hdbody,hdbody',hdecode] using hchild
        next => contradiction

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateProof
