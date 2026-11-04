module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceValidityPrimrecProof
open Source NumberedOriginalSourceCodec NumberedOriginalSourcePresentation

theorem rawShapePrimitive (n : Nat) : Primrec (rawSourceShape n) := by
  have hd : Primrec (fun value : Nat => NumberedNumericDecoding.decodeCode n (Nat.unpair value).2) :=
    (NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp (Primrec.snd.comp Primrec.unpair)
  have hb : Primrec (fun p : Nat × NumberedAuxiliaryCoding.Code (Fin n) =>
      NumberedOriginalSourceShape.codeShape p.2) :=
    (NumberedOriginalSourceShapeProof.codeShapePrimitive n).comp Primrec.snd
  have h := Primrec.option_casesOn hd (Primrec.const false) hb.to₂
  exact h.of_eq (fun value => by
    unfold rawSourceShape
    cases NumberedNumericDecoding.decodeCode n (Nat.unpair value).2 <;> rfl)

theorem packedTestPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × Nat => packedSourceTest n arity p.1 p.2) :=
  Primrec.and.comp (NumberedTypedValidityPrimrecProof.numericPackedSuccessPrimitive n arity)
    ((rawShapePrimitive n).comp Primrec.snd)

theorem fixedTestPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : (List Ty × Ty) × Nat => sourceTest n arity p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (List Ty × Ty) × Nat => packedSourceTest n arity p.1.1 p.2) :=
    (packedTestPrimitive n arity).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have ht : Primrec (fun p : (List Ty × Ty) × Nat =>
      decide ((Nat.unpair p.2).1=NumberedLeastCodeRepresentative.typeNumber p.1.2)) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp (Primrec.snd.comp Primrec.fst))).decide
  exact Primrec.and.comp hp ht

theorem fixedValidityPrimitive : NumberedOriginalSourcePresentationTargets.ActualFixedValidityPrimitive := by
  intro n arity
  exact (fixedTestPrimitive n arity).of_eq
    (fun p => NumberedOriginalSourcePresentationSupportProof.fixedValidity n arity p.1.1 p.1.2 p.2)

theorem packedValidityPrimitive : NumberedOriginalSourcePresentationTargets.ActualPackedValidityPrimitive := by
  intro n arity
  exact (packedTestPrimitive n arity).of_eq
    (fun p => NumberedOriginalSourcePresentationSupportProof.packedValidity n arity p.1 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceValidityPrimrecProof
