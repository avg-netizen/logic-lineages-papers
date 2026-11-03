module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecTargets
open Source NumberedAuxiliaryDecoding NumberedTypeCodecPrimrec

def ActualVariableSuccessCalibration : Prop := ∀ (Gamma : List Ty) (tau : Ty) (index : Nat),
  (decodeVariable Gamma tau index).isSome = decide (Gamma[index]?=some tau)

def ActualVariableSuccessPrimitive : Prop := Primrec (fun p : List Ty × Ty × Nat =>
  (decodeVariable p.1 p.2.1 p.2.2).isSome)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecTargets
