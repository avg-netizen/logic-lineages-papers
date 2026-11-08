module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open InternalApplicationValidityStack InternalOriginalStepGuard

/-- A successful packed decode is exactly an original typed term with this payload. -/
theorem targetWitness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (tau : Ty) (payload : Nat) :
    targetValidityValue n arity Gamma (Nat.pair (typeNumber tau) payload) = 1 ↔
      ∃ q : AuxTerm (Fin n) arity Gamma tau, codeNumber (termCode q) = payload := by
  constructor
  · intro h
    cases hd : decodePackedNumber n arity Gamma (Nat.pair (typeNumber tau) payload) with
    | none => simp [targetValidityValue, hd] at h
    | some q =>
      have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma _ q hd
      have hp := Nat.pair_eq_pair.mp he
      have ht := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective hp.1
      rcases q with ⟨sigma, q⟩
      dsimp [packedNumber] at ht hp
      cases ht
      exact ⟨q, hp.2⟩
  · rintro ⟨q, hq⟩
    have hd := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma ⟨tau,q⟩
    simpa [packedNumber, hq, targetValidityValue, hd] using
      congrArg (fun o => o.isSome.toNat) hd

/-- The source witness retains the original universe Boolean. -/
theorem sourceWitness (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (payload : Nat) :
    sourceValidityValue n arity symbols S Gamma (Nat.pair (typeNumber tau) payload) = 1 ↔
      ∃ q : AuxTerm (Fin n) arity Gamma tau,
        codeNumber (termCode q) = payload ∧ universeTest symbols S q = true := by
  constructor
  · intro h
    cases hd : decodeUniverse n arity symbols S Gamma (Nat.pair (typeNumber tau) payload) with
    | none => simp [sourceValidityValue, rawCarrierTest, hd] at h
    | some q =>
      have hf := Option.filter_eq_some_iff.mp hd
      have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma _ q hf.1
      have hp := Nat.pair_eq_pair.mp he
      have ht := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective hp.1
      rcases q with ⟨sigma,q⟩
      dsimp [packedNumber] at ht hp
      cases ht
      exact ⟨q,hp.2,hf.2⟩
  · rintro ⟨q,hq,hu⟩
    have hd := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma ⟨tau,q⟩
    have he : decodePackedNumber n arity Gamma (Nat.pair (typeNumber tau) payload) = some ⟨tau,q⟩ := by
      simpa [packedNumber,hq] using hd
    simp [sourceValidityValue,rawCarrierTest,decodeUniverse,he,hu]

theorem applicationWitness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (fp ap : Nat) :
    (∃ q : AuxTerm (Fin n) arity Gamma tau,
      codeNumber (termCode q) = Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair fp ap))) ↔
    (∃ f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau), codeNumber (termCode f) = fp) ∧
    (∃ a : AuxTerm (Fin n) arity Gamma sigma, codeNumber (termCode a) = ap) := by
  constructor
  · rintro ⟨q,hq⟩
    cases q with
    | app f a =>
      simp [termCode,codeNumber,Nat.pair_eq_pair] at hq
      have ht := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective hq.1
      cases ht
      exact ⟨⟨f,hq.2.1⟩,⟨a,hq.2.2⟩⟩
    | _ => simp [termCode,codeNumber,Nat.pair_eq_pair] at hq
  · rintro ⟨⟨f,hf⟩,⟨a,ha⟩⟩
    exact ⟨.app f a,by simp [termCode,codeNumber,hf,ha]⟩

theorem applicationSourceWitness (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty) (fp ap : Nat) :
    (∃ q : AuxTerm (Fin n) arity Gamma tau,
      codeNumber (termCode q) = Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair fp ap)) ∧
      universeTest symbols S q = true) ↔
    tau ∈ S ∧
    (∃ f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau),
      codeNumber (termCode f) = fp ∧ universeTest symbols S f = true) ∧
    (∃ a : AuxTerm (Fin n) arity Gamma sigma,
      codeNumber (termCode a) = ap ∧ universeTest symbols S a = true) := by
  constructor
  · rintro ⟨q,hq,hu⟩
    cases q with
    | app f a =>
      simp [termCode,codeNumber,Nat.pair_eq_pair] at hq
      have ht := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective hq.1
      cases ht
      simp only [universeTest,Bool.and_eq_true,decide_eq_true_eq] at hu
      exact ⟨hu.1.1,⟨f,hq.2.1,hu.1.2⟩,⟨a,hq.2.2,hu.2⟩⟩
    | _ => simp [termCode,codeNumber,Nat.pair_eq_pair] at hq
  · rintro ⟨ht,⟨f,hf,uf⟩,⟨a,ha,ua⟩⟩
    exact ⟨.app f a,by simp [termCode,codeNumber,hf,ha],by simp [universeTest,ht,uf,ua]⟩

theorem boolValueZero (b : Bool) (h : b.toNat ≠ 1) : b.toNat = 0 := by
  cases b <;> simp_all

theorem actualOriginalApplicationDecoderEquations :
    InternalApplicationValidityStackTargets.ActualOriginalApplicationDecoderEquations := by
  intro n arity symbols S Gamma d e fp ap
  obtain ⟨sigma,_,hd⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal d
  obtain ⟨tau,ht,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal e
  rw [← hd,← he]
  have htarget := applicationWitness n arity Gamma sigma tau fp ap
  have hsource := applicationSourceWitness n arity symbols S Gamma sigma tau fp ap
  have hmem : InternalStructuralEndpointGuard.membershipValue S (typeNumber tau) = 1 ↔ tau ∈ S := by
    simp [InternalStructuralEndpointGuard.membershipValue,NumberedNumericDecodingSupportProof.typeRoundTrip tau]
  simp only [← targetWitness,← sourceWitness] at htarget hsource
  have htar : targetValidityValue n arity Gamma (applicationValue (typeNumber sigma) (typeNumber tau) fp ap) = 1 ↔
      targetValidityValue n arity Gamma (functionValue (typeNumber sigma) (typeNumber tau) fp) = 1 ∧
      targetValidityValue n arity Gamma (argumentValue (typeNumber sigma) ap) = 1 := by
    simpa [applicationValue,functionValue,argumentValue,typeNumber] using htarget
  have hsrc : sourceValidityValue n arity symbols S Gamma (applicationValue (typeNumber sigma) (typeNumber tau) fp ap) = 1 ↔
      InternalStructuralEndpointGuard.membershipValue S (typeNumber tau) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (functionValue (typeNumber sigma) (typeNumber tau) fp) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (argumentValue (typeNumber sigma) ap) = 1 := by
    simpa [applicationValue,functionValue,argumentValue,typeNumber,hmem] using hsource
  constructor
  · split
    · next h => exact htar.mpr h
    · next h =>
        have hn : targetValidityValue n arity Gamma (applicationValue (typeNumber sigma) (typeNumber tau) fp ap) ≠ 1 := fun he => h (htar.mp he)
        unfold targetValidityValue at hn ⊢
        exact boolValueZero _ hn
  · split
    · next h => exact hsrc.mpr h
    · next h =>
        have hn : sourceValidityValue n arity symbols S Gamma (applicationValue (typeNumber sigma) (typeNumber tau) fp ap) ≠ 1 := fun he => h (hsrc.mp he)
        unfold sourceValidityValue at hn ⊢
        exact boolValueZero _ hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
