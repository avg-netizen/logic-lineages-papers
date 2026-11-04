module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootLeavesPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecProof
open Source NumberedNumericDecoding NumberedDirectCertificate NumberedNumericRoot
open NumberedNumericRootPrimrec NumberedNumericRootLeavesPrimrecProof

attribute [local irreducible] Primrec

abbrev Input (n : Nat) := Window n × (Fin n → Fin n → Bool) × Nat × Nat × Nat

theorem rootDispatchPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Input n =>
      rootDispatch n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hsource : Primrec (fun p : Input n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htarget : Primrec (fun p : Input n => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hcertificate : Primrec (fun p : Input n => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htag : Primrec (fun p : Input n => (Nat.unpair p.2.2.2.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hcertificate)
  have hpayload : Primrec (fun p : Input n => (Nat.unpair p.2.2.2.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hcertificate)
  have hbasic : Primrec (fun p : Input n => (p.1, p.2.2.1, p.2.2.2.1)) :=
    Primrec.fst.pair (hsource.pair htarget)
  have hput : Primrec (fun p : Input n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma (.put (Nat.unpair p.2.2.2.2).2)
        p.2.2.1 p.2.2.2.1) :=
    (putNumericPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1, (Nat.unpair p.2.2.2.2).2, p.2.2.1, p.2.2.2.1))
      (Primrec.fst.pair (hpayload.pair (hsource.pair htarget)))
  have habstraction : Primrec (fun p : Input n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .abstraction p.2.2.1 p.2.2.2.1) :=
    (abstractionNumericPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1, p.2.2.1, p.2.2.2.1)) hbasic
  have hbeta : Primrec (fun p : Input n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .beta p.2.2.1 p.2.2.2.1) :=
    (betaNumericPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1, p.2.2.1, p.2.2.2.1)) hbasic
  have hbottom : Primrec (fun p : Input n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .bottom p.2.2.1 p.2.2.2.1) :=
    (bottomNumericPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1, p.2.2.1, p.2.2.2.1)) hbasic
  have hindex : Primrec (fun p : Input n => (Nat.unpair (Nat.unpair p.2.2.2.2).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htypes : Primrec (fun p : Input n => decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2).2).1) :=
    NumberedTypeCodecPrimrecProof.typeListDecoderPrimitive.comp
      (g := fun p : Input n => (Nat.unpair (Nat.unpair p.2.2.2.2).2).1)
      (Primrec.fst.comp (Primrec.unpair.comp hpayload))
  have hselectBody : Primrec (fun p : Input n × List Ty =>
      selectNumericTest n arity p.1.1.1 p.1.1.2 Gamma p.2
        (Nat.unpair (Nat.unpair p.1.2.2.2.2).2).2 p.1.2.2.1 p.1.2.2.2.1) :=
    (selectNumericPrimitive n arity Gamma).comp
      (g := fun p : Input n × List Ty =>
        (p.1.1, p.2, (Nat.unpair (Nat.unpair p.1.2.2.2.2).2).2, p.1.2.2.1, p.1.2.2.2.1))
      ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair ((hindex.comp Primrec.fst).pair
          ((hsource.comp Primrec.fst).pair (htarget.comp Primrec.fst)))))
  have hselect : Primrec (fun p : Input n =>
      (decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2).2).1).any (fun types =>
        selectNumericTest n arity p.1.1 p.1.2 Gamma types
          (Nat.unpair (Nat.unpair p.2.2.2.2).2).2 p.2.2.1 p.2.2.2.1)) :=
    optionAnyPrimitive htypes hselectBody.to₂
  have hcopy : Primrec (fun p : Input n =>
      NumberedCopyCertificate.copyCertificateTest n arity p.1.1 p.1.2 Gamma p.2.1
        p.2.2.1 p.2.2.2.1 (Nat.unpair p.2.2.2.2).2) :=
    (NumberedCopyOperationProof.numericCopyCertificatePrimitive n arity Gamma).comp
      (g := fun p : Input n =>
        (p.1, p.2.1, p.2.2.1, p.2.2.2.1, (Nat.unpair p.2.2.2.2).2))
      (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
        (hsource.pair (htarget.pair hpayload))))
  have hmul : Primrec (fun p : Input n =>
      NumberedNumericMul.numericMulTest n arity p.1.1 p.1.2 Gamma
        p.2.2.1 p.2.2.2.1 (Nat.unpair p.2.2.2.2).2) :=
    (NumberedMulPrimrecProof.numericMulPrimitive n arity Gamma).comp
      (g := fun p : Input n => (p.1, p.2.2.1, p.2.2.2.1, (Nat.unpair p.2.2.2.2).2))
      (Primrec.fst.pair (hsource.pair (htarget.pair hpayload)))
  have htagEq (k : Nat) : PrimrecPred (fun p : Input n => (Nat.unpair p.2.2.2.2).1 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hzero : PrimrecPred (fun p : Input n => (Nat.unpair p.2.2.2.2).2 = 0) :=
    Primrec.eq.comp hpayload (Primrec.const 0)
  have hdispatch : Primrec (fun p : Input n =>
      if (Nat.unpair p.2.2.2.2).1 = 0 then
        directNumericTest n arity p.1.1 p.1.2 Gamma (.put (Nat.unpair p.2.2.2.2).2)
          p.2.2.1 p.2.2.2.1
      else if (Nat.unpair p.2.2.2.2).1 = 1 then
        if (Nat.unpair p.2.2.2.2).2 = 0 then
          directNumericTest n arity p.1.1 p.1.2 Gamma .abstraction p.2.2.1 p.2.2.2.1
        else false
      else if (Nat.unpair p.2.2.2.2).1 = 2 then
        if (Nat.unpair p.2.2.2.2).2 = 0 then
          directNumericTest n arity p.1.1 p.1.2 Gamma .beta p.2.2.1 p.2.2.2.1
        else false
      else if (Nat.unpair p.2.2.2.2).1 = 3 then
        if (Nat.unpair p.2.2.2.2).2 = 0 then
          directNumericTest n arity p.1.1 p.1.2 Gamma .bottom p.2.2.1 p.2.2.2.1
        else false
      else if (Nat.unpair p.2.2.2.2).1 = 4 then
        (decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2).2).1).any (fun types =>
          selectNumericTest n arity p.1.1 p.1.2 Gamma types
            (Nat.unpair (Nat.unpair p.2.2.2.2).2).2 p.2.2.1 p.2.2.2.1)
      else if (Nat.unpair p.2.2.2.2).1 = 5 then
        NumberedCopyCertificate.copyCertificateTest n arity p.1.1 p.1.2 Gamma p.2.1
          p.2.2.1 p.2.2.2.1 (Nat.unpair p.2.2.2.2).2
      else if (Nat.unpair p.2.2.2.2).1 = 6 then
        NumberedNumericMul.numericMulTest n arity p.1.1 p.1.2 Gamma
          p.2.2.1 p.2.2.2.1 (Nat.unpair p.2.2.2.2).2
      else false) :=
    Primrec.ite (htagEq 0) hput
      (Primrec.ite (htagEq 1) (Primrec.ite hzero habstraction (Primrec.const false))
        (Primrec.ite (htagEq 2) (Primrec.ite hzero hbeta (Primrec.const false))
          (Primrec.ite (htagEq 3) (Primrec.ite hzero hbottom (Primrec.const false))
            (Primrec.ite (htagEq 4) hselect
              (Primrec.ite (htagEq 5) hcopy
                (Primrec.ite (htagEq 6) hmul (Primrec.const false)))))))
  apply hdispatch.of_eq
  intro p
  unfold rootDispatch
  generalize Nat.unpair p.2.2.2.2 = parts
  rcases parts with ⟨tag, payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag <;> cases payload <;> rfl

theorem numericRootPrimitive : NumberedNumericRootPrimrecTargets.ActualNumericRootPrimitive := by
  intro n arity Gamma
  exact (rootDispatchPrimitive n arity Gamma).of_eq (fun p =>
    NumberedNumericRootPrimrecSupportProof.rootDispatchCalibration n arity p.1.1 p.1.2 Gamma
      p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecProof
