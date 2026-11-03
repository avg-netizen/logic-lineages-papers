module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecProof
open Source NumberedAuxiliaryDecoding NumberedTypeCodecPrimrec

theorem variableSuccessCalibration : NumberedVariableDecoderPrimrecTargets.ActualVariableSuccessCalibration := by
  intro Gamma
  induction Gamma with
  | nil => intro tau index; cases index <;> rfl
  | cons sigma Gamma ih =>
    intro tau index
    cases index with
    | zero =>
      by_cases h : sigma=tau <;> simp [decodeVariable,h]
    | succ index =>
      rw [decodeVariable,Option.isSome_map]
      convert ih tau index using 1
      simp

theorem variableSuccessPrimitive : NumberedVariableDecoderPrimrecTargets.ActualVariableSuccessPrimitive := by
  have h : Primrec (fun p : List Ty × Ty × Nat => decide (p.1[p.2.2]?=some p.2.1)) :=
    (Primrec.eq.comp (Primrec.list_getElem?.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))).decide
  exact h.of_eq (fun p => (variableSuccessCalibration p.1 p.2.1 p.2.2).symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecProof
