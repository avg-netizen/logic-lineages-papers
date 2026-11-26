module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedTypedFocus NumberedStepContexts NumberedStepCertificate
open NumberedNumericRoot NumberedDirectCertificate

/-- The original empty-focus checker retains both the requested typed target
and the literal replacement number. Its direct beta selector has no window
guard, so this statement needs no universe or window hypothesis. -/
theorem typedBetaCertificateIff (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (a : AuxTerm (Fin n) arity Gamma sigma) (r : AuxTerm (Fin n) arity Gamma tau)
    (replacement : Nat) :
    stepTest n arity symbols S Gamma table (.app (.lam body) a) r
      ⟨[],replacement,Nat.pair 2 0⟩ = true ↔
        r = substitute body (singleSubstitution a) ∧
        replacement = packedNumber
          (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) := by
  have hs : decodeSelector n arity Gamma (Nat.pair 2 0) = some (.direct .beta) := by
    simp [decodeSelector]
  constructor
  · intro h
    cases hb : decodePackedNumber n arity Gamma replacement with
    | none => simp [stepTest,focus,hb] at h
    | some b =>
      obtain ⟨rho,b⟩ := b
      simp only [stepTest,focus,hb,hs] at h
      split at h
      next ht =>
        cases ht
        have hh : (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) =
            ⟨tau,b⟩ ∧
            packedNumber (⟨tau,b⟩ : Packed (Fin n) arity Gamma) =
              packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by
          simpa [selectorTest,directTarget,plug] using h
        have hbr : b = r := by
          simpa using NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hh.2
        have hresult : substitute body (singleSubstitution a) = b := by
          simpa using hh.1
        have hnumber := NumberedNumericDecodingProof.packedNumericSound n arity Gamma replacement
          (⟨tau,b⟩ : Packed (Fin n) arity Gamma) hb
        refine ⟨hbr.symm.trans hresult.symm,?_⟩
        rw [← hresult] at hnumber
        exact hnumber.symm
      next => contradiction
  · rintro ⟨rfl,rfl⟩
    have hb := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
      (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma)
    simp [stepTest,focus,hb,hs,selectorTest,directTarget,plug]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCertificateTypedProof
