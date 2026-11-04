module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepCodePrimrecProof
open Source NumberedAuxiliaryCoding NumberedTypedFocus NumberedStepCertificate
open NumberedUniformPackedDecoding NumberedUniformSelector NumberedFocusCode NumberedNumericStepPrimrec
open NumberedNumericRootLeavesPrimrecProof

attribute [local irreducible] Primrec

abbrev Window (n : Nat) := List (Fin n) × List Ty
abbrev StepInput (n : Nat) :=
  (Window n × (Fin n → Fin n → Bool)) ×
    (List Ty × Ty × Code (Fin n) × Code (Fin n)) × StepCertificate

theorem stepCodePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : StepInput n =>
      stepCodeTest n arity p.1.1.1 p.1.1.2 p.2.1.1 p.1.2
        p.2.1.2.1 p.2.1.2.2.1 p.2.1.2.2.2 p.2.2) := by
  let B := StepInput n × RawValue (Fin n)
  let C := B × RawPacked n
  have hwindow : Primrec (fun p : StepInput n => p.1.1) := Primrec.fst.comp Primrec.fst
  have htable : Primrec (fun p : StepInput n => p.1.2) := Primrec.snd.comp Primrec.fst
  have hGamma : Primrec (fun p : StepInput n => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have htau : Primrec (fun p : StepInput n => p.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hsource : Primrec (fun p : StepInput n => p.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have htarget : Primrec (fun p : StepInput n => p.2.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hcertificate : Primrec (fun p : StepInput n =>
      NumberedStepCodecPrimrec.certificateEquiv p.2.2) :=
    NumberedStepCodecPrimrecSupportProof.certificateTo.comp (Primrec.snd.comp Primrec.snd)
  have hpath : Primrec (fun p : StepInput n => p.2.2.path) := Primrec.fst.comp hcertificate
  have hreplacement : Primrec (fun p : StepInput n => p.2.2.replacement) :=
    Primrec.fst.comp (Primrec.snd.comp hcertificate)
  have hroot : Primrec (fun p : StepInput n => p.2.2.root) :=
    Primrec.snd.comp (Primrec.snd.comp hcertificate)
  have hfocus : Primrec (fun p : StepInput n =>
      focusCode p.2.2.path p.2.1.1 p.2.1.2.1 p.2.1.2.2.1) :=
    (NumberedFocusCodePrimrecProof.focusPrimitive n).comp
      (g := fun p : StepInput n => (p.2.2.path,p.2.1.1,p.2.1.2.1,p.2.1.2.2.1))
      (hpath.pair (hGamma.pair (htau.pair hsource)))
  have hdecode : Primrec (fun p : B =>
      rawPackedDecode n arity p.2.1 p.1.2.2.replacement) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp
      (g := fun p : B => (p.2.1,p.1.2.2.replacement))
      ((Primrec.fst.comp Primrec.snd).pair (hreplacement.comp Primrec.fst))
  have hdata : Primrec (fun p : C => p.1.1) := Primrec.fst.comp Primrec.fst
  have hfocused : Primrec (fun p : C => p.1.2) := Primrec.snd.comp Primrec.fst
  have hselector := (NumberedUniformSelectorProof.selectorPrimitive n arity).comp
    (g := fun p : C =>
      (p.1.1.1.1,p.1.1.1.2,p.1.2.1,p.1.2.2,p.2,p.1.1.2.2.root))
    ((hwindow.comp hdata).pair ((htable.comp hdata).pair
      ((Primrec.fst.comp hfocused).pair ((Primrec.snd.comp hfocused).pair
        (Primrec.snd.pair (hroot.comp hdata))))))
  have hreplace := (NumberedFocusCodePrimrecProof.replacementPrimitive n).comp
    (g := fun p : C =>
      ((p.1.1.2.2.path,p.1.1.2.1.1,p.1.1.2.1.2.1,p.1.1.2.1.2.2.1),p.2.2))
    (((hpath.comp hdata).pair ((hGamma.comp hdata).pair
      ((htau.comp hdata).pair (hsource.comp hdata)))).pair (Primrec.snd.comp Primrec.snd))
  have hcompare : Primrec (fun p : C =>
      decide (replaceCode p.1.1.2.2.path p.1.1.2.1.1 p.1.1.2.1.2.1
        p.1.1.2.1.2.2.1 p.2.2 = some p.1.1.2.1.2.2.2)) :=
    (Primrec.eq.comp hreplace (Primrec.option_some.comp (htarget.comp hdata))).decide
  have hguard : PrimrecPred (fun p : C => p.2.1 = p.1.2.2.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp hfocused))
  have hbody : Primrec (fun p : C =>
      if p.2.1 = p.1.2.2.1 then
        selectorCodeTest n arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.2.1 p.1.1.1.2
          p.1.2.2 p.2 p.1.1.2.2.root &&
          decide (replaceCode p.1.1.2.2.path p.1.1.2.1.1 p.1.1.2.1.2.1
            p.1.1.2.1.2.2.1 p.2.2 = some p.1.1.2.1.2.2.2)
      else false) :=
    Primrec.ite hguard (Primrec.and.comp hselector hcompare) (Primrec.const false)
  have hinner : Primrec (fun p : B =>
      (rawPackedDecode n arity p.2.1 p.1.2.2.replacement).any (fun replacement =>
        if replacement.1 = p.2.2.1 then
          selectorCodeTest n arity p.1.1.1.1 p.1.1.1.2 p.2.1 p.1.1.2
            p.2.2 replacement p.1.2.2.root &&
            decide (replaceCode p.1.2.2.path p.1.2.1.1 p.1.2.1.2.1
              p.1.2.1.2.2.1 replacement.2 = some p.1.2.1.2.2.2)
        else false)) :=
    optionAnyPrimitive hdecode hbody.to₂
  exact optionAnyPrimitive hfocus hinner.to₂

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepCodePrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepCodePrimrecProof
