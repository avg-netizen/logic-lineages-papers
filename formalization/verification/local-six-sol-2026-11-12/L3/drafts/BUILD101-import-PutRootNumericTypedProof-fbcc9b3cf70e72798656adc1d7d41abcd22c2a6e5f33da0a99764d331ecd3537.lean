module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootCorrectedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedAuxiliaryCoding NumberedNumericDecoding NumberedTypedFocus NumberedStepContexts
open NumberedStepCertificate NumberedNumericRoot NumberedDirectCertificate PutRoot

/-- Empty focus with the ORIGINAL PUT selector forces an ordinary source,
its exact numbered target, and the SAME literal replacement bytes. -/
theorem typedPutSound (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau) (label replacement : Nat)
    (h : stepTest n arity symbols S Gamma table q r ⟨[],replacement,Nat.pair 0 label⟩ = true) :
    (Nat.unpair (codeNumber (termCode q))).1 = 4 ∧
      packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) =
        resultValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) label ∧
      replacement = resultValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) label := by
  have hs : decodeSelector n arity Gamma (Nat.pair 0 label) = some (.direct (.put label)) := by
    simp [decodeSelector]
  cases hb : decodePackedNumber n arity Gamma replacement with
  | none => simp [stepTest,focus,hb] at h
  | some b =>
    obtain ⟨rho,b⟩ := b
    simp only [stepTest,focus,hb,hs] at h
    split at h
    next ht =>
      cases ht
      have hh : directTarget arity Gamma (.put label) (⟨tau,q⟩ : Packed (Fin n) arity Gamma) = some ⟨tau,b⟩ ∧
          packedNumber (⟨tau,b⟩ : Packed (Fin n) arity Gamma) =
            packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by
        simpa [selectorTest,plug] using h
      have hnumber := NumberedNumericDecodingProof.packedNumericSound n arity Gamma replacement
        (⟨tau,b⟩ : Packed (Fin n) arity Gamma) hb
      have hinstance := (NumberedDirectCertificateProof.directRuleCheck n arity Gamma (.put label)
        (⟨tau,q⟩ : Packed (Fin n) arity Gamma) (⟨tau,b⟩ : Packed (Fin n) arity Gamma)).mp hh.1
      cases hinstance with
      | put label head base =>
        have hresult : packedNumber
            (⟨headResult head,.numbered label head (headResult head) base [] .nil⟩ : Packed (Fin n) arity Gamma) =
            resultValue (packedNumber
              (⟨headResult head,.ordinary head base⟩ : Packed (Fin n) arity Gamma)) label := by
          simp [resultValue,packedNumber,termCode,codeNumber,typesNumber]
        exact ⟨by simp [termCode,codeNumber],hh.2.symm.trans hresult,hnumber.symm.trans hresult⟩
    next => contradiction
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericTypedProof
