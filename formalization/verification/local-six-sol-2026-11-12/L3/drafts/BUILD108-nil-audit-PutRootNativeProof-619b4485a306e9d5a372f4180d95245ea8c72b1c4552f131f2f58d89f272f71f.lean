module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNativeProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open NumberedNumericStep NumberedStepCertificate NumberedNumericRoot NumberedTypedFocus
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection PutRoot
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Under the actual original source decoder, the raw ordinary tag selects
precisely the original typed ordinary constructor. -/
theorem chosenCertificateAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (ho : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4)
    (ht : v.get 1 = resultValue (v.get 0) (labelValue (v.get 2)))
    (hk : v.get 2 = certificateValue (v.get 0) (labelValue (v.get 2))) :
    leafValue n arity v = 1 := by
  classical
  obtain ⟨Gamma,hGamma⟩ := InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
    (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none =>
    simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,decodedValue,hc] at hs
    contradiction
  | some ctx =>
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none =>
      simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        decodedValue,hc,hGamma,rawCarrierTest,hq,Option.isSome_none,Bool.toNat_false] at hs
      contradiction
    | some q =>
      obtain ⟨tau,q⟩ := q
      have source := (NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma
        (v.get 0) (⟨tau,q⟩ : Packed (Fin n) arity Gamma)).mp hq
      have he := source.1
      have htag : (Nat.unpair (codeNumber (termCode q))).1 = 4 := by
        rw [← he] at ho
        simpa only [packedNumber,Nat.unpair_pair] using ho
      cases q with
      | ordinary head base =>
        have hnumeric := PutRootNumericProof.actualOriginalNumericPutCertificate n arity ctx.1.1
          ctx.1.2 Gamma ctx.2 head base (labelValue (v.get 2))
          (v.get 1) (resultValue (v.get 0) (labelValue (v.get 2)))
        have hresult : resultValue (v.get 0) (labelValue (v.get 2)) = packedNumber
            (⟨headResult head,.numbered (labelValue (v.get 2)) head (headResult head) base [] .nil⟩ : Packed (Fin n) arity Gamma) := by
          rw [← he]
          simp [resultValue,packedNumber,termCode,codeNumber,typesNumber]
        have hchosen : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
            (v.get 0) (v.get 1) (certificateValue (v.get 0) (labelValue (v.get 2))) = true := by
          rw [he] at hnumeric
          rw [certificateValue,hnumeric]
          simp only [decide_eq_true_eq]
          exact ⟨source.2,ht.trans hresult,hresult⟩
        have htest : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
            (v.get 0) (v.get 1) (v.get 2) = true :=
          (congrArg (fun k => numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
            (v.get 0) (v.get 1) k) hk).trans hchosen
        simp only [leafValue,hc,hGamma,htest,Bool.toNat_true]
      | var => simp [termCode,codeNumber] at htag
      | lam => simp [termCode,codeNumber] at htag
      | app => simp [termCode,codeNumber] at htag
      | bottom => simp [termCode,codeNumber] at htag
      | numbered => simp [termCode,codeNumber] at htag

/-- Accepted arbitrary old certificates in the active PUT branch force its
ordinary source tag and exact target. No source or target shape is assumed. -/
theorem chosenCertificateSound (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1)
    (hk : v.get 2 = certificateValue (v.get 0) (labelValue (v.get 2))) :
    (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 ∧
      v.get 1 = resultValue (v.get 0) (labelValue (v.get 2)) := by
  obtain ⟨Gamma,hGamma⟩ := InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
    (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none => simp only [leafValue,hc] at ha; contradiction
  | some ctx =>
    have hstep : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) = true := by
      simp only [leafValue,hc,hGamma] at ha
      cases h : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all only [Bool.toNat_false,Bool.toNat_true,Nat.zero_ne_one]
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none => simp only [numericStepTest,hq] at hstep; contradiction
    | some q =>
      obtain ⟨tau,q⟩ := q
      have he := ((NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma
        (v.get 0) (⟨tau,q⟩ : Packed (Fin n) arity Gamma)).mp hq).1
      let label := labelValue (v.get 2)
      let cert : StepCertificate := ⟨[],resultValue (v.get 0) label,Nat.pair 0 label⟩
      have hcert : decodeStepCertificate (v.get 2) = some cert := by
        exact (congrArg decodeStepCertificate hk).trans
          (NumberedNumericStepProof.stepCertificateNumericRoundTrip cert)
      cases hr : decodePackedNumber n arity Gamma (v.get 1) with
      | none => simp only [numericStepTest,hq,hr] at hstep; contradiction
      | some r =>
        obtain ⟨rho,r⟩ := r
        simp only [numericStepTest,hq,hr,hcert] at hstep
        split at hstep
        next ht =>
          cases ht
          have sound := PutRootNumericTypedProof.typedPutSound n arity ctx.1.1 ctx.1.2 Gamma ctx.2
            tau q r label (resultValue (v.get 0) label) hstep
          have htarget := NumberedNumericDecodingProof.packedNumericSound n arity Gamma
            (v.get 1) (⟨tau,r⟩ : Packed (Fin n) arity Gamma) hr
          constructor
          · rw [← he]
            simpa only [packedNumber,Nat.unpair_pair] using sound.1
          · have h := htarget.symm.trans sound.2.1
            simpa only [he] using h
        next => contradiction
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNativeProof
