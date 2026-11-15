module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem listEncoding {alpha : Type} [Encodable alpha] (xs : List alpha) :
    Encodable.encode xs = numbersNumber (xs.map Encodable.encode) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,ih,List.map_cons,numbersNumber]
    omega

theorem typeInverseEncoding (raw : Nat) :
    Encodable.encode (NumberedTypeCodecPrimrec.typeEquiv.symm raw) = raw :=
  NumberedTypeCodecPrimrec.typeEquiv.apply_symm_apply raw

theorem originalTypeListImage (raw : Nat) : ∃ xs : List Source.Ty, Encodable.encode xs = raw := by
  obtain ⟨nums,he⟩ := NumberedMultisetNumericTotalityProof.encodingSurjective raw
  refine ⟨nums.map NumberedTypeCodecPrimrec.typeEquiv.symm,?_⟩
  rw [listEncoding,List.map_map]
  have hf : (Encodable.encode ∘ NumberedTypeCodecPrimrec.typeEquiv.symm) = (fun x : Nat => x) := by
    funext x
    exact typeInverseEncoding x
  rw [hf]
  change numbersNumber (nums.map id) = raw
  rw [List.map_id]
  exact he

theorem tuplesEncoding (types : List Source.Ty) (count : Nat) :
    NumericProof.tuples (types.map Encodable.encode) count =
      (NumberedAuxiliaryEnumeration.typeLists types count).map Encodable.encode := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [NumericProof.tuples,NumberedAuxiliaryEnumeration.typeLists,ih,List.map_cons,
      Encodable.encode_list_nil,List.map_flatMap,List.flatMap_map,List.map_map]
    congr 1
    apply congrArg (fun f => types.flatMap f)
    funext tau
    apply congrArg (fun f => (NumberedAuxiliaryEnumeration.typeLists types count).map f)
    funext xs
    simp only [Function.comp_apply,Encodable.encode_list_cons,Nat.succ_eq_add_one,Nat.add_comm]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
