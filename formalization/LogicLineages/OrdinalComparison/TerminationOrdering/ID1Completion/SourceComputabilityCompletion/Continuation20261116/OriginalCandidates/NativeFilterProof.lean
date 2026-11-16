module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeNumericProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeFilterProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedLeastCodeRepresentative
open NumberedUniformPackedDecoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open TwoSol20261113.CalibratedPrimary.Membership (entriesCode)

theorem packedValue (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (Gamma : List Source.Ty) (q : RawPacked n) :
    evaluate (OriginalTypedDecoder.packedCheck H) (ofFn ![Encodable.encode q,Encodable.encode Gamma]) =
      (decodeTerm arity Gamma q.1 q.2).isSome.toNat := by
  rw [OriginalTypedDecoderCalibrationProof.packedCalibration n arity H hH]
  change OriginalTypedDecoder.packedDecoderValue n arity (Nat.pair (typeNumber q.1) (codeNumber q.2)) (Encodable.encode Gamma) = _
  rw [OriginalTypedDecoderCalibrationValuesProof.packedValue]
  simp only [Nat.unpair_pair,OriginalTypedDecoder.termDecoderValue,Encodable.encodek,
    NumberedNumericDecodingSupportProof.typeRoundTrip,NumberedNumericDecodingProof.codeRoundTrip]

theorem retainedList (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (Gamma : List Source.Ty) (xs : List (RawPacked n)) :
    (xs.map Encodable.encode).filter (fun candidate => decide (evaluate (OriginalTypedDecoder.packedCheck H)
      (ofFn ![candidate,Encodable.encode Gamma]) ≠ 0)) =
      (xs.filterMap (rawStructuralDecode arity Gamma)).map Encodable.encode := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    rw [List.map_cons,List.filter_cons,packedValue n arity H hH]
    cases hd : decodeTerm arity Gamma q.1 q.2 <;>
      simp [rawStructuralDecode,hd] at ih ⊢ <;> exact ih

theorem filterOriginal (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (Gamma : List Source.Ty) (xs : List (RawPacked n)) :
    evaluate (filterCandidates H) (ofFn ![entriesCode xs,Encodable.encode Gamma]) =
      entriesCode (xs.filterMap (rawStructuralDecode arity Gamma)) := by
  unfold entriesCode
  rw [NativeNumericProof.filterValue,retainedList n arity H hH]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeFilterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeFilterProof
