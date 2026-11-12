module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNativeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open NumberedNumericStep NumberedStepCertificate NumberedNumericRoot NumberedTypedFocus
open NumberedDirectCertificate NumberedStepContexts
open OriginalTransparentVariableStepEvaluationProof (bottomValue certificateValue)
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The explicit nil-path/direct-bottom certificate works for every typed
nonbottom source, not merely variables. -/
theorem numericCertificate (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau)
    (hq : decodeUniverse n arity symbols S Gamma
      (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) = some ⟨tau,q⟩)
    (hn : q ≠ .bottom tau) :
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma))
      (bottomValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)))
      (certificateValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma))) = true := by
  let bottom : Packed (Fin n) arity Gamma := ⟨tau,AuxTerm.bottom tau⟩
  let selector : RootSelector n arity Gamma := .direct .bottom
  let cert : StepCertificate := ⟨[],packedNumber bottom,selectorNumber selector⟩
  have hb : bottomValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) =
      packedNumber bottom := by simp [bottomValue,bottom,packedNumber,termCode,codeNumber]
  have hc : certificateValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) =
      stepCertificateNumber cert := by
    simp [certificateValue,hb,stepCertificateNumber,cert,pathNumber,
      NumberedMultisetNumeric.numbersNumber,selector,selectorNumber]
  have hd : directTarget arity Gamma .bottom (⟨tau,q⟩ : Packed (Fin n) arity Gamma) = some bottom := by
    cases q <;> simp_all [directTarget,bottom]
  rw [hb,hc]
  have hbdecode := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma bottom
  have hcdecode := NumberedNumericStepProof.stepCertificateNumericRoundTrip cert
  have hsdecode := NumberedNumericRootProof.rootSelectorRoundTrip n arity Gamma selector
  simp only [numericStepTest,hq,hbdecode,hcdecode,bottom,↓reduceDIte]
  simp [stepTest,cert,focus,hbdecode,hsdecode,selector,selectorTest,hd,plug,bottom]

theorem chosenCertificateAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (hn : BottomRepresentative.bottomValue (v.get 0) ≠ 1)
    (ht : v.get 1 = bottomValue (v.get 0))
    (hk : v.get 2 = certificateValue (v.get 0)) : leafValue n arity v = 1 := by
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
      have he := ((NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma
        (v.get 0) ⟨tau,q⟩).mp hq).1
      have hnot : q ≠ .bottom tau := by
        intro heq
        subst q
        apply hn
        rw [← he]
        simp [BottomRepresentative.bottomValue,packedNumber,termCode,codeNumber]
      have hq' : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma
          (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) = some ⟨tau,q⟩ := by
        simpa only [he] using hq
      have ha := numericCertificate n arity ctx.1.1 ctx.1.2 Gamma ctx.2 tau q hq' hnot
      rw [he] at ha
      simp only [leafValue,hc,hGamma,ht,hk,ha]
      rfl

/-- With this exact empty certificate, acceptance forces the literal target
code, even when arbitrary target bytes were supplied. -/
theorem chosenCertificateTarget (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1)
    (hk : v.get 2 = certificateValue (v.get 0)) : v.get 1 = bottomValue (v.get 0) := by
  obtain ⟨Gamma,hGamma⟩ := InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
    (v.get 0) (v.get 3)
  cases hctx : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none =>
    simp only [leafValue,hctx] at ha
    contradiction
  | some ctx =>
    have hstep : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) = true := by
      simp only [leafValue,hctx,hGamma] at ha
      cases h : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all only [Bool.toNat_false,Bool.toNat_true,Nat.zero_ne_one]
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none => simp only [numericStepTest,hq] at hstep; contradiction
    | some q =>
      obtain ⟨tau,q⟩ := q
      have he := ((NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma
        (v.get 0) ⟨tau,q⟩).mp hq).1
      let bottom : Packed (Fin n) arity Gamma := ⟨tau,AuxTerm.bottom tau⟩
      let selector : RootSelector n arity Gamma := .direct .bottom
      let cert : StepCertificate := ⟨[],packedNumber bottom,selectorNumber selector⟩
      have hb : bottomValue (v.get 0) = packedNumber bottom := by
        rw [← he]
        simp [bottomValue,bottom,packedNumber,termCode,codeNumber]
      have hcert : v.get 2 = stepCertificateNumber cert := by
        rw [hk]
        simp [certificateValue,hb,stepCertificateNumber,cert,pathNumber,
          NumberedMultisetNumeric.numbersNumber,selector,selectorNumber]
      have hcdecode := NumberedNumericStepProof.stepCertificateNumericRoundTrip cert
      have hbdecode := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma bottom
      have hsdecode := NumberedNumericRootProof.rootSelectorRoundTrip n arity Gamma selector
      cases hr : decodePackedNumber n arity Gamma (v.get 1) with
      | none => simp only [numericStepTest,hq,hr] at hstep; contradiction
      | some r =>
        obtain ⟨rho,r⟩ := r
        simp only [numericStepTest,hq,hr,hcert,hcdecode] at hstep
        split at hstep
        next htype =>
          cases htype
          have htarget := NumberedNumericDecodingProof.packedNumericSound n arity Gamma
            (v.get 1) ⟨tau,r⟩ hr
          have heq : packedNumber bottom = packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by
            have htest := hstep
            simp only [stepTest,cert,focus,hbdecode,hsdecode,bottom,↓reduceDIte,plug] at htest
            exact of_decide_eq_true (Bool.and_eq_true.mp htest).2
          exact htarget.symm.trans (heq.symm.trans hb.symm)
        next => contradiction

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNativeProof
