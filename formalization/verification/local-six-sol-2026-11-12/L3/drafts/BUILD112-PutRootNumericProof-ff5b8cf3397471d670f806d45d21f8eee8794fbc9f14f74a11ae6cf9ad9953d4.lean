module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedAuxiliaryCoding NumberedStepCertificate NumberedNumericStep NumberedNumericRoot
open NumberedTypedFocus NumberedStepContexts NumberedDirectCertificate PutRoot PutRootWorkingTargets

/-- Full ORIGINAL numeric test, including failed source-universe membership
and arbitrary target/replacement numbers. -/
theorem actualOriginalNumericPutCertificate : ActualOriginalNumericPutCertificate := by
  classical
  intro n arity symbols S Gamma table head base label target replacement
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  let q : Packed (Fin n) arity Gamma := ⟨headResult head,.ordinary head base⟩
  let r : Packed (Fin n) arity Gamma := ⟨headResult head,.numbered label head (headResult head) base [] .nil⟩
  let cert : StepCertificate := ⟨[],replacement,Nat.pair 0 label⟩
  have hc : decodeStepCertificate (Nat.pair 0 (Nat.pair replacement (Nat.pair 0 label))) = some cert :=
    stepCertificateNumericRoundTrip cert
  have hresult : resultValue (packedNumber q) label = packedNumber r := by
    simp [q,r,resultValue,packedNumber,termCode,argumentsCode,codeNumber,typesNumber]
  constructor
  · intro h
    cases hq : decodeUniverse n arity symbols S Gamma (packedNumber q) with
    | none => simp [numericStepTest,hq] at h
    | some value =>
      have hsource := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
        (packedNumber q) value).mp hq
      have he : value = q := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hsource.1
      subst value
      refine ⟨hsource.2,?_⟩
      cases hr : decodePackedNumber n arity Gamma target with
      | none => simp [numericStepTest,hq,hr] at h
      | some other =>
        obtain ⟨rho,other⟩ := other
        simp only [numericStepTest,hq,hr,hc] at h
        split at h
        next ht =>
          cases ht
          have sound := PutRootNumericTypedProof.typedPutSound n arity symbols S Gamma table
            (headResult head) (.ordinary head base) other label replacement h
          have htarget := NumberedNumericDecodingProof.packedNumericSound n arity Gamma target
            (⟨headResult head,other⟩ : Packed (Fin n) arity Gamma) hr
          exact ⟨htarget.symm.trans (sound.2.1.trans hresult),sound.2.2.trans hresult⟩
        next => contradiction
  · rintro ⟨hsource,rfl,rfl⟩
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (packedNumber q) q).mpr ⟨rfl,hsource⟩
    have hr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r
    have hcert := stepCertificateNumericRoundTrip (⟨[],packedNumber r,Nat.pair 0 label⟩ : StepCertificate)
    have hs : decodeSelector n arity Gamma (Nat.pair 0 label) = some (.direct (.put label)) := by
      simp [decodeSelector]
    simp [numericStepTest,hq,hr,hcert,stepTest,focus,hs,selectorTest,directTarget,plug,q,r]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericProof
