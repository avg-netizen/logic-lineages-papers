module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedCopyCertificate NumberedRootDecomposition
open NumberedTypedFocus NumberedStepContexts NumberedStepCertificate NumberedNumericDecoding NumberedNumericRoot
open OriginalLambdaCertificate

theorem actualTypedLambdaCertificateLift :
    OriginalLambdaCertificateTargets.ActualTypedLambdaCertificateLift := by
  intro n arity symbols S Gamma table sigma tau body body' child
  cases hf : focus child.path body with
  | none => simp [stepTest,liftCertificate,focus,hf]
  | some f =>
    cases hb : decodePackedNumber n arity f.holeGamma child.replacement with
    | none => simp [stepTest,liftCertificate,focus,hf,hb]
    | some b =>
      obtain ⟨beta,b⟩ := b
      cases hs : decodeSelector n arity f.holeGamma child.root with
      | none => simp [stepTest,liftCertificate,focus,hf,hb,hs]
      | some selector =>
        simp only [stepTest,liftCertificate,focus,hf,Option.map_some,hb,hs]
        split
        next ht =>
          cases ht
          simp [plug,packedNumber,termCode,codeNumber]
        next _ => simp

/-- Read the root instance from the replacement and selector in the given
empty-path certificate. No completeness theorem selects another witness. -/
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

/-- Generalize the packed endpoints before eliminating root constructors.
The original syntax tag rules out every non-bottom root at a lambda. -/
theorem rootLambdaTagBottom {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S Gamma : List Ty} {above : Fin n → Fin n → Prop}
    {q r : Packed (Fin n) arity Gamma}
    (h : RootInstance n arity symbols S above Gamma q r)
    (htag : (Nat.unpair (codeNumber (termCode q.2))).1 = 1) :
    r = ⟨q.1,.bottom q.1⟩ := by
  cases h with
  | direct rule q r hd =>
    cases hd with
    | put label f base => simp [termCode,codeNumber] at htag
    | abstraction k f sigma tau base types extras => simp [termCode,codeNumber] at htag
    | beta sigma tau body a => simp [termCode,codeNumber] at htag
    | bottom tau q hb => rfl
  | select q r hs =>
    cases hs with
    | select k f tau base extraTypes extras types selected hm =>
      simp [termCode,codeNumber] at htag
  | mul q r hm =>
    cases hm with
    | mul k f g base types extras target he hw hm => simp [termCode,codeNumber] at htag
  | copy k f g base types extras he hw => simp [termCode,codeNumber] at htag

theorem rootLambdaBottom (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (above : Fin n → Fin n → Prop) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (target : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (h : RootInstance n arity symbols S above Gamma
      ⟨.arrow sigma tau,.lam body⟩ ⟨.arrow sigma tau,target⟩) :
    target = .bottom (.arrow sigma tau) := by
  have hp := rootLambdaTagBottom h (by simp [termCode,codeNumber])
  simpa using hp

theorem actualTypedLambdaCertificateRootBottom :
    OriginalLambdaCertificateTargets.ActualTypedLambdaCertificateRootBottom := by
  intro n arity symbols S Gamma table sigma tau body target replacement root h
  exact rootLambdaBottom n arity symbols S Gamma (tableAbove table) sigma tau body target
    (emptyPathRoot n arity symbols S Gamma table (.arrow sigma tau)
      (.lam body) target replacement root h)

theorem actualLambdaCertificateOtherPositionRejected :
    OriginalLambdaCertificateTargets.ActualLambdaCertificateOtherPositionRejected := by
  intro n arity Gamma sigma tau body position rest hn
  cases position with
  | lam => exact False.elim (hn rfl)
  | appFunction => unfold focus <;> rfl
  | ordinaryBase index => unfold focus <;> rfl
  | numberedBase index => unfold focus <;> rfl
  | numberedExtras index => unfold focus <;> rfl

theorem actualTypedLambdaCertificateNonbottomInversion :
    OriginalLambdaCertificateTargets.ActualTypedLambdaCertificateNonbottomInversion := by
  intro n arity symbols S Gamma table sigma tau body target certificate hn h
  have hs := NumberedStepCertificateProof.stepCertificateSound n arity symbols S Gamma table
    (.arrow sigma tau) (.lam body) target certificate h
  rcases (NumberedLambdaRootProof.actualLambdaStepCases
    (Fin n) arity symbols S (tableAbove table) Gamma sigma tau body target).mp hs with
      hb | ⟨body',_,hr⟩
  · exact False.elim (hn hb)
  · subst target
    rcases certificate with ⟨path,replacement,root⟩
    cases path with
    | nil =>
      have hb := actualTypedLambdaCertificateRootBottom n arity symbols S Gamma table
        sigma tau body (.lam body') replacement root h
      cases hb
    | cons position rest =>
      cases position with
      | lam =>
        refine ⟨body',rest,rfl,rfl,?_⟩
        exact (actualTypedLambdaCertificateLift n arity symbols S Gamma table
          sigma tau body body' ⟨rest,replacement,root⟩).symm.trans h
      | appFunction => simp [stepTest,focus] at h
      | ordinaryBase index =>
        simp only [stepTest] at h
        unfold focus at h
        contradiction
      | numberedBase index => simp [stepTest,focus] at h
      | numberedExtras index => simp [stepTest,focus] at h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTypedProof
