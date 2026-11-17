module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.PermissiveGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.NativeProof
open Source NumberedLeastCodeRepresentative NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem codeGuards : Targets.NativeCodeGuards := by
  unfold Targets.NativeCodeGuards
  constructor <;> rw [Continuation20261115.OriginalCodeValidityGuard.NativeProof.nativeValidity,
    NumberedNumericDecodingProof.codeRoundTrip] <;> rfl

theorem headMove : Targets.NativeHeadMove := by
  unfold Targets.NativeHeadMove
  rw [Continuation20261114.OriginalHeadMove.NativeProof.nativeHeadMove]
  decide

theorem resultEquality : Targets.NativeResultEquality := by
  exact Continuation20261114.OriginalHeadResult.NativeProof.nativeHeadResult 0 head

theorem checkerDecoder (q : NumberedAuxiliaryCoding.Code (Fin 0)) :
    evaluate checker (input q) =
      (NumberedAuxiliaryDecoding.decodeTerm arity [] ground q).isSome.toNat := by
  unfold checker input
  rw [PermissiveGuardProof.checkerEqualsTyped,
    OriginalTypedDecoderCalibrationProof.termCalibration 0 arity _
      (Continuation20261116.OriginalConcreteHeadSignature.NativeProof.nativeSignature 0 arity)]
  change OriginalTypedDecoder.termDecoderValue 0 arity (typeNumber ground)
    (codeNumber q) (Encodable.encode ([] : List Ty)) = _
  simp only [OriginalTypedDecoder.termDecoderValue, Encodable.encodek,
    NumberedNumericDecodingProof.typeNumericRoundTrip, NumberedNumericDecodingProof.codeRoundTrip]

theorem sourceSuccess : Targets.NativeSourceSuccess := by
  unfold Targets.NativeSourceSuccess
  rw [checkerDecoder]
  rfl

theorem targetFailure : Targets.NativeTargetFailure := by
  unfold Targets.NativeTargetFailure
  rw [checkerDecoder]
  rfl

theorem diagnostic : Targets.NativeDiagnostic :=
  ⟨codeGuards, headMove, resultEquality, sourceSuccess, targetFailure⟩
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.NativeProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.NativeProof
