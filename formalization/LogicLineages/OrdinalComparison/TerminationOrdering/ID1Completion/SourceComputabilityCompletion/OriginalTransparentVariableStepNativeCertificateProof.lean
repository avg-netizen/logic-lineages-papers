module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open NumberedNumericStep NumberedStepCertificate NumberedNumericRoot NumberedTypedFocus
open NumberedDirectCertificate NumberedStepContexts
open OriginalTransparentVariableStepEvaluationProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A native certificate is explicitly the original nil path and direct
bottom selector. It is not merely a certificate obtained by completeness. -/
theorem variableNumericCertificate (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (tau : Ty) (name : Variable Gamma tau)
    (hq : decodeUniverse n arity symbols S Gamma
      (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma)) =
        some ⟨tau,AuxTerm.var name⟩) :
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma))
      (bottomValue (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma)))
      (certificateValue (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma))) = true := by
  let bottom : Packed (Fin n) arity Gamma := ⟨tau,AuxTerm.bottom tau⟩
  let selector : RootSelector n arity Gamma := .direct .bottom
  let cert : StepCertificate := ⟨[],packedNumber bottom,selectorNumber selector⟩
  have hb : bottomValue (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma)) =
      packedNumber bottom := by simp [bottomValue,bottom,packedNumber,termCode,codeNumber]
  have hc : certificateValue (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma)) =
      stepCertificateNumber cert := by
    simp [certificateValue,hb,stepCertificateNumber,cert,pathNumber,
      NumberedMultisetNumeric.numbersNumber,selector,selectorNumber]
  rw [hb,hc]
  have hbdecode := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma bottom
  have hcdecode := NumberedNumericStepProof.stepCertificateNumericRoundTrip cert
  have hsdecode := NumberedNumericRootProof.rootSelectorRoundTrip n arity Gamma selector
  simp only [numericStepTest,hq,hbdecode,hcdecode,bottom,↓reduceDIte]
  simp [stepTest,cert,focus,hbdecode,hsdecode,selector,selectorTest,directTarget,plug,bottom]

/-- An accepted original numeric leaf always pays the original source
validity; this handles malformed contexts without assuming a successful parse. -/
theorem acceptedSource (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (h : leafValue n arity v = 1) :
    sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 := by
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none => simp only [leafValue,hc] at h
            contradiction
  | some ctx =>
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none =>
      simp only [leafValue,hc,hGamma,numericStepTest,hq,Bool.toNat_false] at h
      contradiction
    | some q =>
      simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        decodedValue,hc,hGamma,rawCarrierTest,hq,Option.isSome_some,Bool.toNat_true]

/-- Exact certificate success follows from original source acceptance and
its variable tag. The literal replacement/selector are constructed above. -/
theorem chosenCertificateAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (hv : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (ht : v.get 1 = bottomValue (v.get 0))
    (hk : v.get 2 = certificateValue (v.get 0)) : leafValue n arity v = 1 := by
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none =>
    simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
      decodedValue,hc] at hs
    contradiction
  | some ctx =>
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none =>
      simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
        decodedValue,hc,hGamma,rawCarrierTest,hq,Option.isSome_none,Bool.toNat_false] at hs
      contradiction
    | some q =>
      obtain ⟨tau,q⟩ := q
      have he : packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma) = v.get 0 :=
        ((NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma
          (v.get 0) ⟨tau,q⟩).mp hq).1
      rw [← he] at hv
      cases q
      case var name =>
        have hq' : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma
            (packedNumber (⟨tau,AuxTerm.var name⟩ : Packed (Fin n) arity Gamma)) =
              some ⟨tau,AuxTerm.var name⟩ := by simpa only [he] using hq
        have ha := variableNumericCertificate n arity ctx.1.1 ctx.1.2 Gamma ctx.2 tau name hq'
        rw [he] at ha
        simp only [leafValue,hc,hGamma,ht,hk,ha]
        rfl
      all_goals simp [packedNumber,termCode,codeNumber] at hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
