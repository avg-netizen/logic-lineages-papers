module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction
open NumberedLeastCodeRepresentative NumberedCopyCertificate NumberedRootDecomposition
open NumberedTypedFocus NumberedStepContexts NumberedStepCertificate NumberedNumericStep
open NumberedNumericDecoding NumberedNumericCarrier NumberedNumericRoot NumberedPrimaryShapes
open ApplicationCertificateLift

/-- Empty original focus paths certify an actual root rule. The replacement
and selector are decoded from this certificate, not obtained by completeness. -/
theorem emptyPathRoot (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau) (replacement root : Nat)
    (h : stepTest n arity symbols S Gamma table q r ⟨[],replacement,root⟩ = true) :
    RootInstance n arity symbols S (tableAbove table) Gamma ⟨tau,q⟩ ⟨tau,r⟩ := by
  cases hb : decodePackedNumber n arity Gamma replacement with
  | none => simp [stepTest,focus,hb] at h
  | some b =>
    obtain ⟨sigma,b⟩ := b
    cases hc : decodeSelector n arity Gamma root with
    | none => simp [stepTest,focus,hb,hc] at h
    | some selector =>
      simp only [stepTest,focus,hb,hc] at h
      split at h
      next ht =>
        cases ht
        have hh : selectorTest n arity symbols S Gamma table ⟨tau,q⟩ ⟨tau,b⟩ selector = true ∧
            packedNumber (⟨tau,b⟩ : Packed (Fin n) arity Gamma) =
              packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by
          simpa [plug] using h
        have hr := (NumberedNumericRootProof.typedRootSelectors n arity symbols S Gamma table
          ⟨tau,q⟩ ⟨tau,b⟩).mp ⟨selector,hh.1⟩
        have he : b = r := by
          simpa using NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hh.2
        subst b
        exact hr
      next => contradiction

/-- At a non-lambda application, the only original root rule is bottom.
Function-context reduction cannot be inserted into the root-rule judgment. -/
theorem rootNeutralBottom (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (above : Fin n → Fin n → Prop) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (r : AuxTerm (Fin n) arity Gamma tau)
    (hn : isLambda f = false)
    (h : RootInstance n arity symbols S above Gamma ⟨tau,.app f a⟩ ⟨tau,r⟩) :
    r = .bottom tau := by
  cases h with
  | direct rule q r hd =>
    cases hd with
    | beta sigma tau body a => cases hn
    | bottom tau q hb => rfl
  | select q r hs => cases hs
  | mul q r hm => cases hm

theorem actualTypedNeutralCertificateInversion :
    OriginalNeutralCertificateTargets.ActualTypedNeutralCertificateInversion := by
  intro n arity symbols S Gamma table sigma tau f a r c hn h
  have hs := NumberedStepCertificateProof.stepCertificateSound n arity symbols S Gamma table
    tau (.app f a) r c h
  rcases (NumberedNonLambdaApplicationProof.actualNonLambdaApplicationStep
    (Fin n) arity symbols S (tableAbove table) Gamma sigma tau f a r hn).mp hs with
    hb | ⟨g,_,hr⟩
  · exact Or.inl hb
  · right
    subst r
    rcases c with ⟨path,replacement,root⟩
    cases path with
    | nil =>
      have hr := emptyPathRoot n arity symbols S Gamma table tau (.app f a) (.app g a)
        replacement root h
      have hb := rootNeutralBottom n arity symbols S Gamma (tableAbove table)
        sigma tau f a (.app g a) hn hr
      cases hb
    | cons position path =>
      cases position with
      | lam => simp [stepTest,focus] at h
      | appFunction =>
        refine ⟨g,⟨path,replacement,root⟩,rfl,rfl,?_⟩
        exact (ApplicationCertificateLiftProof.actualTypedLift n arity symbols S Gamma table
          sigma tau f g a ⟨path,replacement,root⟩).symm.trans h
      | ordinaryBase index => simp [stepTest,focus] at h
      | numberedBase index => simp [stepTest,focus] at h
      | numberedExtras index => simp [stepTest,focus] at h

theorem actualNumericNeutralCertificateInversion :
    OriginalNeutralCertificateTargets.ActualNumericNeutralCertificateInversion := by
  intro n arity symbols S Gamma table sigma tau f a target certificate hn h
  cases hq : decodeUniverse n arity symbols S Gamma
      (packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma)) with
  | none => simp [numericStepTest,hq] at h
  | some q =>
    have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma)) q).mp hq
    have he : q = (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma) :=
      NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hsource.1
    subst q
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
          rcases actualTypedNeutralCertificateInversion n arity symbols S Gamma table
            sigma tau f a r c hn h with hb | ⟨g,child,hresult,hcertificate,hchild⟩
          · left
            subst r
            exact (NumberedNumericDecodingProof.packedNumericSound n arity Gamma target
              ⟨tau,.bottom tau⟩ hr).symm
          · right
            refine ⟨g,stepCertificateNumber child,?_,?_,?_⟩
            · rw [hresult] at hr
              exact (NumberedNumericDecodingProof.packedNumericSound n arity Gamma target
                ⟨tau,.app g a⟩ hr).symm
            · have he := NumberedNumericStepProof.stepCertificateNumericSound certificate c hc
              rw [hcertificate] at he
              exact he.symm.trans (ApplicationCertificateLiftProof.actualStepEncoding child).symm
            · have hf : InUniverse symbols S f := ⟨hsource.2.1.2.1,hsource.2.2.1⟩
              have hdf := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
                (packedNumber (⟨.arrow sigma tau,f⟩ : Packed (Fin n) arity Gamma))
                ⟨.arrow sigma tau,f⟩).mpr ⟨rfl,hf⟩
              have hdg := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
                (⟨.arrow sigma tau,g⟩ : Packed (Fin n) arity Gamma)
              have hdk := NumberedNumericStepProof.stepCertificateNumericRoundTrip child
              simpa [numericStepTest,hdf,hdg,hdk] using hchild
        next => contradiction

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralCertificateProof
