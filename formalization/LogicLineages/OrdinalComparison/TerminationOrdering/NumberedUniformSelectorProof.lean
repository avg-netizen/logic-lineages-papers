module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedNumericDecoding NumberedMultisetNumeric NumberedNumericRoot
open NumberedUniformPackedDecoding NumberedUniformSelector NumberedUniformSelectorSupportProof
open NumberedDirectOperations NumberedAuxiliarySubstitution NumberedSelfApplication NumberedCopyOperation
open NumberedNumericRootLeavesPrimrecProof

theorem selectorCalibration : NumberedUniformSelectorTargets.ActualSelectorCalibration := by
  intro n arity symbols S Gamma table q r certificate
  unfold selectorCodeTest
  generalize hparts : Nat.unpair certificate = parts
  rcases parts with ⟨tag,payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag
  · simpa only [decodeSelector,hparts,Option.any_some,selectorTest,packedCode] using
      putCalibration n arity Gamma payload q r
  · cases payload with
    | zero => simpa only [decodeSelector,hparts,Option.any_some,selectorTest,packedCode] using
        abstractionCalibration n arity Gamma q r
    | succ payload => simp [decodeSelector,hparts]
  · cases payload with
    | zero => simpa only [decodeSelector,hparts,Option.any_some,selectorTest,packedCode] using
        betaCalibration n arity Gamma q r
    | succ payload => simp [decodeSelector,hparts]
  · cases payload with
    | zero => simpa only [decodeSelector,hparts,Option.any_some,selectorTest,packedCode] using
        bottomCalibration n arity Gamma q r
    | succ payload => simp [decodeSelector,hparts]
  · simp only [decodeSelector,hparts]
    cases decodeTypes (Nat.unpair payload).1 with
    | none => rfl
    | some types =>
      simpa only [Option.map_some,Option.any_some,selectorTest,packedCode] using
        selectCalibration n arity Gamma types (Nat.unpair payload).2 q r
  · simp only [decodeSelector,hparts]
    cases decodeHeadNumber n payload with
    | none => rfl
    | some head =>
      simpa only [Option.map_some,Option.any_some,selectorTest,packedCode] using
        copyCalibration n arity symbols S Gamma table head q r
  · simp only [decodeSelector,hparts,packedCode]
    rw [NumberedUniformMulProof.mulTestCalibration n arity symbols S Gamma q r payload]
    cases decodeCertificate n arity Gamma payload <;> rfl
  · simp [decodeSelector,hparts]

attribute [local irreducible] Primrec

abbrev Input (n : Nat) :=
  (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) ×
    List Ty × RawPacked n × RawPacked n × Nat

theorem selectorPrimitive : NumberedUniformSelectorTargets.ActualSelectorPrimitive := by
  intro n arity
  have htable : Primrec (fun p : Input n => p.2.1) := Primrec.fst.comp Primrec.snd
  have hGamma : Primrec (fun p : Input n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsource : Primrec (fun p : Input n => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htarget : Primrec (fun p : Input n => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hcertificate : Primrec (fun p : Input n => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htau : Primrec (fun p : Input n => p.2.2.2.1.1) := Primrec.fst.comp hsource
  have hcode : Primrec (fun p : Input n => p.2.2.2.1.2) := Primrec.snd.comp hsource
  have htag : Primrec (fun p : Input n => (Nat.unpair p.2.2.2.2.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hcertificate)
  have hpayload : Primrec (fun p : Input n => (Nat.unpair p.2.2.2.2.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hcertificate)
  have hputCode : Primrec (fun p : Input n =>
      putCode (Nat.unpair p.2.2.2.2.2).2 p.2.2.2.1.1 p.2.2.2.1.2) :=
    (NumberedDirectCodePrimrecProof.putCodePrimitive n).comp
      (g := fun p : Input n => ((Nat.unpair p.2.2.2.2.2).2,p.2.2.2.1.1,p.2.2.2.1.2))
      (hpayload.pair (htau.pair hcode))
  have hput : Primrec (fun p : Input n =>
      outputCodeTest p.2.2.2.1.1
        (putCode (Nat.unpair p.2.2.2.2.2).2 p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1) :=
    (outputCodePrimitive n).comp (htau.pair (hputCode.pair htarget))
  have habstractionCode : Primrec (fun p : Input n => abstractionCode p.2.2.2.1.2) :=
    (NumberedDirectCodePrimrecProof.allAbstractionCodePrimitive n).comp
      (g := fun p : Input n => p.2.2.2.1.2) hcode
  have habstraction : Primrec (fun p : Input n =>
      outputCodeTest p.2.2.2.1.1 (abstractionCode p.2.2.2.1.2) p.2.2.2.2.1) :=
    (outputCodePrimitive n).comp (htau.pair (habstractionCode.pair htarget))
  have hbetaCode : Primrec (fun p : Input n => betaCode p.2.2.1.length p.2.2.2.1.2) :=
    (NumberedAuxiliaryBetaPrimrecProof.allBetaCodePrimitive n).comp
      (Primrec.list_length.comp hGamma) hcode
  have hbeta : Primrec (fun p : Input n =>
      outputCodeTest p.2.2.2.1.1 (betaCode p.2.2.1.length p.2.2.2.1.2) p.2.2.2.2.1) :=
    (outputCodePrimitive n).comp (htau.pair (hbetaCode.pair htarget))
  have hbottomCode : Primrec (fun p : Input n => bottomCode p.2.2.2.1.1 p.2.2.2.1.2) :=
    (NumberedDirectCodePrimrecProof.bottomCodePrimitive n).comp
      (g := fun p : Input n => (p.2.2.2.1.1,p.2.2.2.1.2)) (htau.pair hcode)
  have hbottom : Primrec (fun p : Input n =>
      outputCodeTest p.2.2.2.1.1 (bottomCode p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1) :=
    (outputCodePrimitive n).comp (htau.pair (hbottomCode.pair htarget))
  have hindex : Primrec (fun p : Input n => (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htypes : Primrec (fun p : Input n => decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).1) :=
    NumberedTypeCodecPrimrecProof.typeListDecoderPrimitive.comp
      (g := fun p : Input n => (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).1)
      (Primrec.fst.comp (Primrec.unpair.comp hpayload))
  have hselectCode : Primrec (fun p : Input n × List Ty =>
      selectCode p.2 (Nat.unpair (Nat.unpair p.1.2.2.2.2.2).2).2
        p.1.2.2.2.1.1 p.1.2.2.2.1.2) :=
    (NumberedSelectCodePrimrecProof.allSelectCodePrimitive n).comp
      (g := fun p : Input n × List Ty =>
        (p.2,(Nat.unpair (Nat.unpair p.1.2.2.2.2.2).2).2,p.1.2.2.2.1.1,p.1.2.2.2.1.2))
      (Primrec.snd.pair ((hindex.comp Primrec.fst).pair
        ((htau.comp Primrec.fst).pair (hcode.comp Primrec.fst))))
  have hselectBody : Primrec (fun p : Input n × List Ty =>
      outputCodeTest p.1.2.2.2.1.1
        (selectCode p.2 (Nat.unpair (Nat.unpair p.1.2.2.2.2.2).2).2
          p.1.2.2.2.1.1 p.1.2.2.2.1.2) p.1.2.2.2.2.1) :=
    (outputCodePrimitive n).comp
      ((htau.comp Primrec.fst).pair (hselectCode.pair (htarget.comp Primrec.fst)))
  have hselect : Primrec (fun p : Input n =>
      (decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).1).any (fun types =>
        outputCodeTest p.2.2.2.1.1
          (selectCode types (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).2
            p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1)) :=
    optionAnyPrimitive htypes hselectBody.to₂
  have hcopyCode : Primrec (fun p : Input n × HeadCode (Fin n) =>
      copyCode arity p.1.1.1 p.1.1.2 p.1.2.1 p.2 p.1.2.2.2.1.2) :=
    (NumberedCopyOperationProof.allCopyCodePrimitive n arity).comp
      (g := fun p : Input n × HeadCode (Fin n) =>
        (p.1.1,(p.1.2.1,p.2),p.1.2.2.2.1.2))
      ((Primrec.fst.comp Primrec.fst).pair
        (((htable.comp Primrec.fst).pair Primrec.snd).pair (hcode.comp Primrec.fst)))
  have hcopyBody : Primrec (fun p : Input n × HeadCode (Fin n) =>
      outputCodeTest p.1.2.2.2.1.1
        (copyCode arity p.1.1.1 p.1.1.2 p.1.2.1 p.2 p.1.2.2.2.1.2) p.1.2.2.2.2.1) :=
    (outputCodePrimitive n).comp
      ((htau.comp Primrec.fst).pair (hcopyCode.pair (htarget.comp Primrec.fst)))
  have hcopy : Primrec (fun p : Input n =>
      (decodeHeadNumber n (Nat.unpair p.2.2.2.2.2).2).any (fun head =>
        outputCodeTest p.2.2.2.1.1
          (copyCode arity p.1.1 p.1.2 p.2.1 head p.2.2.2.1.2) p.2.2.2.2.1)) :=
    optionAnyPrimitive ((NumberedHeadCodecPrimrecProof.headDecoderPrimitive n).comp hpayload) hcopyBody.to₂
  have hmul : Primrec (fun p : Input n =>
      NumberedUniformMul.mulTest n arity p.1.1 p.1.2 p.2.2.1
        p.2.2.2.1.2 p.2.2.2.2.1.2 (Nat.unpair p.2.2.2.2.2).2) :=
    (NumberedUniformMulProof.mulTestPrimitive n arity).comp
      (g := fun p : Input n =>
        (p.1,p.2.2.1,p.2.2.2.1.2,p.2.2.2.2.1.2,(Nat.unpair p.2.2.2.2.2).2))
      (Primrec.fst.pair (hGamma.pair (hcode.pair ((Primrec.snd.comp htarget).pair hpayload))))
  have htagEq (k : Nat) : PrimrecPred (fun p : Input n => (Nat.unpair p.2.2.2.2.2).1 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hzero : PrimrecPred (fun p : Input n => (Nat.unpair p.2.2.2.2.2).2 = 0) :=
    Primrec.eq.comp hpayload (Primrec.const 0)
  have hdispatch : Primrec (fun p : Input n =>
      if (Nat.unpair p.2.2.2.2.2).1 = 0 then
        outputCodeTest p.2.2.2.1.1
          (putCode (Nat.unpair p.2.2.2.2.2).2 p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1
      else if (Nat.unpair p.2.2.2.2.2).1 = 1 then
        if (Nat.unpair p.2.2.2.2.2).2 = 0 then
          outputCodeTest p.2.2.2.1.1 (abstractionCode p.2.2.2.1.2) p.2.2.2.2.1 else false
      else if (Nat.unpair p.2.2.2.2.2).1 = 2 then
        if (Nat.unpair p.2.2.2.2.2).2 = 0 then
          outputCodeTest p.2.2.2.1.1 (betaCode p.2.2.1.length p.2.2.2.1.2) p.2.2.2.2.1 else false
      else if (Nat.unpair p.2.2.2.2.2).1 = 3 then
        if (Nat.unpair p.2.2.2.2.2).2 = 0 then
          outputCodeTest p.2.2.2.1.1 (bottomCode p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1 else false
      else if (Nat.unpair p.2.2.2.2.2).1 = 4 then
        (decodeTypes (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).1).any (fun types =>
          outputCodeTest p.2.2.2.1.1
            (selectCode types (Nat.unpair (Nat.unpair p.2.2.2.2.2).2).2
              p.2.2.2.1.1 p.2.2.2.1.2) p.2.2.2.2.1)
      else if (Nat.unpair p.2.2.2.2.2).1 = 5 then
        (decodeHeadNumber n (Nat.unpair p.2.2.2.2.2).2).any (fun head =>
          outputCodeTest p.2.2.2.1.1
            (copyCode arity p.1.1 p.1.2 p.2.1 head p.2.2.2.1.2) p.2.2.2.2.1)
      else if (Nat.unpair p.2.2.2.2.2).1 = 6 then
        NumberedUniformMul.mulTest n arity p.1.1 p.1.2 p.2.2.1
          p.2.2.2.1.2 p.2.2.2.2.1.2 (Nat.unpair p.2.2.2.2.2).2
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
  unfold selectorCodeTest
  generalize Nat.unpair p.2.2.2.2.2 = parts
  rcases parts with ⟨tag,payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag <;> cases payload <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorProof
