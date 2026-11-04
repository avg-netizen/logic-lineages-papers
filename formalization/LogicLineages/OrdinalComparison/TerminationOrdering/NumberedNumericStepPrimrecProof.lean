module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepCodePrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
open Source NumberedAuxiliaryCoding NumberedStepCertificate NumberedNumericStep
open NumberedUniformPackedDecoding NumberedNumericStepPrimrec
open NumberedNumericStepCodePrimrecProof NumberedNumericRootLeavesPrimrecProof

attribute [local irreducible] Primrec

abbrev Input (n : Nat) :=
  (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) × List Ty × Nat × Nat × Nat

theorem stepCalibration : NumberedNumericStepPrimrecTargets.ActualStepCalibration :=
  NumberedNumericStepPrimrecSupportProof.stepCalibration

theorem numericStepDispatchPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Input n =>
      numericStepDispatch n arity p.1.1 p.1.2 p.2.2.1 p.2.1
        p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let A := Input n × RawPacked n
  let B := A × RawPacked n
  let C := B × StepCertificate
  have htable : Primrec (fun p : Input n => p.2.1) := Primrec.fst.comp Primrec.snd
  have hGamma : Primrec (fun p : Input n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsource : Primrec (fun p : Input n => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htarget : Primrec (fun p : Input n => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hcertificate : Primrec (fun p : Input n => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hsourceDecode : Primrec (fun p : Input n =>
      rawUniverseDecode n arity p.1.1 p.1.2 p.2.2.1 p.2.2.2.1) :=
    (NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity).comp
      (g := fun p : Input n => (p.1,p.2.2.1,p.2.2.2.1))
      (Primrec.fst.pair (hGamma.pair hsource))
  have htargetDecode : Primrec (fun p : A =>
      rawPackedDecode n arity p.1.2.2.1 p.1.2.2.2.2.1) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp
      (g := fun p : A => (p.1.2.2.1,p.1.2.2.2.2.1))
      ((hGamma.comp Primrec.fst).pair (htarget.comp Primrec.fst))
  have hcertificateDecode : Primrec (fun p : B =>
      decodeStepCertificate p.1.1.2.2.2.2.2) :=
    NumberedStepCodecPrimrecProof.stepDecoderPrimitive.comp
      (g := fun p : B => p.1.1.2.2.2.2.2)
      (hcertificate.comp (Primrec.fst.comp Primrec.fst))
  have hdata : Primrec (fun p : C => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hsourceRaw : Primrec (fun p : C => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have htargetRaw : Primrec (fun p : C => p.1.2) := Primrec.snd.comp Primrec.fst
  have hstep := (stepCodePrimitive n arity).comp
    (g := fun p : C =>
      ((p.1.1.1.1,p.1.1.1.2.1),
        (p.1.1.1.2.2.1,p.1.1.2.1,p.1.1.2.2,p.1.2.2),p.2))
    (((Primrec.fst.comp hdata).pair (htable.comp hdata)).pair
      (((hGamma.comp hdata).pair ((Primrec.fst.comp hsourceRaw).pair
        ((Primrec.snd.comp hsourceRaw).pair (Primrec.snd.comp htargetRaw)))).pair Primrec.snd))
  have htype : PrimrecPred (fun p : C => p.1.2.1 = p.1.1.2.1) :=
    Primrec.eq.comp (Primrec.fst.comp htargetRaw) (Primrec.fst.comp hsourceRaw)
  have hchecked : Primrec (fun p : C =>
      if p.1.2.1 = p.1.1.2.1 then
        stepCodeTest n arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2.2.1
          p.1.1.1.2.1 p.1.1.2.1 p.1.1.2.2 p.1.2.2 p.2
      else false) :=
    Primrec.ite htype hstep (Primrec.const false)
  have hcertificateCase := optionAnyPrimitive hcertificateDecode hchecked.to₂
  have htargetCase := optionAnyPrimitive htargetDecode hcertificateCase.to₂
  have hprogram := optionAnyPrimitive hsourceDecode htargetCase.to₂
  apply hprogram.of_eq
  intro p
  unfold numericStepDispatch
  dsimp only
  cases hs : rawUniverseDecode n arity p.1.1 p.1.2 p.2.2.1 p.2.2.2.1 with
  | none => rfl
  | some q =>
    rcases q with ⟨tau,q⟩
    cases ht : rawPackedDecode n arity p.2.2.1 p.2.2.2.2.1 with
    | none => simp only [Option.any_some,ht,Option.any_none]
    | some r =>
      rcases r with ⟨sigma,r⟩
      cases hc : decodeStepCertificate p.2.2.2.2.2 <;>
        simp only [Option.any_some,ht,hc,Option.any_none]

theorem numericStepPrimitive : NumberedNumericStepPrimrecTargets.ActualNumericStepPrimitive := by
  intro n arity
  exact (numericStepDispatchPrimitive n arity).of_eq (fun p =>
    NumberedNumericStepPrimrecSupportProof.numericStepCalibration n arity p.1.1 p.1.2
      p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
