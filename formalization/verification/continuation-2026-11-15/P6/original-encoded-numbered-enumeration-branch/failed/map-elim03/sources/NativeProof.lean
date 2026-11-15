module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open NativeSupportProof

theorem typesEncoding (ts : List Source.Ty) : Encodable.encode ts = typesNumber ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [Encodable.encode_list_cons,ih]
    simp only [typesNumber,OriginalContextExtensionCalibrationProof.typeEncoding,
      Nat.succ_eq_add_one,Nat.add_comm]

theorem numberedEncoding (n : Nat) (k : Nat) (h : HeadCode (Fin n)) (t : Source.Ty)
    (b : Code (Fin n)) (ts : List Source.Ty) (e : Code (Fin n)) :
    Encodable.encode (Code.numbered k h t b ts e) =
      Nat.pair 5 (Nat.pair (Encodable.encode k) (Nat.pair (headNumber h)
        (Nat.pair (Encodable.encode t) (Nat.pair (Encodable.encode b)
          (Nat.pair (Encodable.encode ts) (Encodable.encode e)))))) := by
  simp only [typesEncoding,OriginalContextExtensionCalibrationProof.typeEncoding,Encodable.encode_nat]
  rfl

theorem convertedHeadsEncoding (n : Nat) (heads : List (HeadCode (Fin n))) :
    (heads.map Encodable.encode).map (fun h => evaluate (OriginalEncodedHeadConversion.convert n) (ofFn ![h])) =
      heads.map headNumber := by
  rw [List.map_map]
  apply congrArg (fun f => heads.map f)
  funext h
  exact OriginalEncodedHeadConversion.NativeProof.encodedHead n h

theorem nativeBranch : Targets.NativeBranch := by
  intro n labels heads types bases tuples extras
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  change evaluate (branch n) (inputs (labels.map Encodable.encode) (heads.map Encodable.encode)
    (types.map Encodable.encode) (bases.map Encodable.encode) (tuples.map Encodable.encode)
    (extras.map Encodable.encode)) = _
  rw [branchValue,convertedHeadsEncoding]
  simp only [pairs,List.map_flatMap,List.flatMap_map,List.map_map]
  simp only [Function.comp_def,numberedEncoding]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeProof
