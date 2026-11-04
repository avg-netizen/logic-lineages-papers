module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedOriginalSourceCodec NumberedOriginalSourcePresentation NumberedOriginalSourcePresentationProof
open NumberedOriginalSourceWindow NumberedOriginalSourceWindowSupportProof NumberedOriginalSourceWindowPrimrecProof
open NumberedTypeCodecPrimrec

def numericData (n value : Nat) : Ty × Code (Fin n) :=
  (typeEquiv.symm (Nat.unpair value).1,(decodeCode n (Nat.unpair value).2).getD .argumentsNil)

theorem numericDataPrimitive (n : Nat) : Primrec (numericData n) :=
  (NumberedTypeCodecPrimrecSupportProof.typeFrom.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.option_getD.comp
      ((NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const Code.argumentsNil))

theorem numericDataCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (s : Term (Fin n) arity Gamma tau) :
    numericData n (sourceNumber s)=(tau,termCode (translateOriginal s)) := by
  have ht : typeEquiv.symm (typeNumber tau)=tau := typeEquiv.symm_apply_apply tau
  simp only [numericData,sourceNumber,packedNumber,Nat.unpair_pair,ht,
    NumberedNumericDecodingProof.codeRoundTrip,Option.getD_some]

theorem termWindowPrimitive (n : Nat) : Primrec (fun p : Ty × Code (Fin n) => termWindow p.1 p.2) :=
  (allRequestsPrimitive n).comp Primrec.sumInl

theorem fixedSourceWindowPrimitive : NumberedOriginalSourceWindowTargets.ActualFixedSourceWindowPrimitive := by
  intro n arity Gamma tau
  have he : Primrec (fun s : Term (Fin n) arity Gamma tau => sourceNumber s) := Primrec.encode
  have h := (termWindowPrimitive n).comp ((numericDataPrimitive n).comp he)
  apply h.of_eq
  intro s
  rw [numericDataCalibration n arity Gamma tau s]
  exact literalWindowCalibration (Fin n) arity Gamma tau s

theorem packedSourceWindowPrimitive : NumberedOriginalSourceWindowTargets.ActualPackedSourceWindowPrimitive := by
  intro n arity Gamma
  have he : Primrec (fun p : PackedSource (Fin n) arity Gamma => packedSourceNumber p) := Primrec.encode
  have h := (termWindowPrimitive n).comp ((numericDataPrimitive n).comp he)
  apply h.of_eq
  intro p
  rcases p with ⟨tau,s⟩
  change termWindow (numericData n (sourceNumber s)).1 (numericData n (sourceNumber s)).2=Source.SourcePortContexts.literalTypes s
  rw [numericDataCalibration n arity Gamma tau s]
  exact literalWindowCalibration (Fin n) arity Gamma tau s

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowProof
