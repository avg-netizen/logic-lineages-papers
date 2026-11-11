module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateCodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedStepCertificate NumberedNumericStep OriginalBetaResult

theorem actualOriginalNumericBetaCertificate :
    OriginalBetaResultTargets.ActualOriginalNumericBetaCertificate := by
  classical
  intro n arity symbols S Gamma table sigma tau body a target replacement
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hc := (OriginalBetaResultCertificateCodingProof.actualOriginalBetaCertificateCoding
    replacement).2
  constructor
  · intro h
    cases hq : decodeUniverse n arity symbols S Gamma
        (packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma)) with
    | none => simp [numericStepTest,hq] at h
    | some q =>
      have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
        (packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma)) q).mp hq
      have he : q = (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma) :=
        NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hsource.1
      subst q
      refine ⟨hsource.2,?_⟩
      cases hr : decodePackedNumber n arity Gamma target with
      | none => simp [numericStepTest,hq,hr] at h
      | some r =>
        obtain ⟨rho,r⟩ := r
        simp only [numericStepTest,hq,hr,hc] at h
        split at h
        next ht =>
          cases ht
          obtain ⟨hresult,hreplacement⟩ :=
            (OriginalBetaResultCertificateTypedProof.typedBetaCertificateIff n arity symbols S Gamma
              table sigma tau body a r replacement).mp h
          subst r
          have htarget := NumberedNumericDecodingProof.packedNumericSound n arity Gamma target
            (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) hr
          exact ⟨htarget.symm,hreplacement⟩
        next => contradiction
  · rintro ⟨hsource,rfl,rfl⟩
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma))
      (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma)).mpr ⟨rfl,hsource⟩
    have hr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
      (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma)
    have hstep := (OriginalBetaResultCertificateTypedProof.typedBetaCertificateIff n arity symbols S
      Gamma table sigma tau body a (substitute body (singleSubstitution a))
      (packedNumber (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma))).mpr
        ⟨rfl,rfl⟩
    simpa [numericStepTest,hq,hr,hc] using hstep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateProof
