module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCodePresentation

theorem codeEncodingCalibration : NumberedCodePresentationTargets.ActualCodeEncodingCalibration := by
  intro n code; rfl

theorem codeDecodeNormalization : NumberedCodePresentationTargets.ActualCodeDecodeNormalization := by
  intro n value
  cases h : decodeCode n value with
  | none => simp [encdec,h]
  | some code =>
    have he := NumberedNumericDecodingProof.codeNumericSound n value code h
    unfold encdec
    rw [h]
    change Nat.succ (codeNumber code)=Nat.succ value
    exact congrArg Nat.succ he

theorem codePresentationPrimitive : NumberedCodePresentationTargets.ActualCodePresentationPrimitive := by
  intro n
  have h : Primrec (fun value => bif (decodeCode n value).isSome then value+1 else 0) :=
    Primrec.cond (NumberedCodeParserTableProof.codeDecodeSuccessPrimitive n) Primrec.succ (Primrec.const 0)
  exact Primrec.nat_iff.mp (h.of_eq (fun value => (codeDecodeNormalization n value).symm))

instance codePrimcodable (n : Nat) : Primcodable (Code (Fin n)) where
  toEncodable := codeEncodable n
  prim := codePresentationPrimitive n

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationProof
