module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeBranchesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeHeadsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedCodeEnumerationPrimrecSupportProof (cross)
open NativeSupportProof NativeBranchesProof
variable (n : Nat) (types : List Source.Ty) (heads : List (HeadCode (Fin n)))
    (labels tupleBound variableBound : Nat) (prior opened : List (Code (Fin n)))

theorem convertedHeadsValue :
    evaluate (convertedHeads n) (inputs types heads labels tupleBound variableBound prior opened) =
      Encodable.encode (heads.map headNumber) := by
  change evaluate (InternalListMap.map (OriginalEncodedHeadConversion.convert n)) (ofFn ![Encodable.encode heads]) = _
  apply mapEncoding
  intro h
  simp only [Encodable.encode_nat]
  exact OriginalEncodedHeadConversion.NativeProof.encodedHead n h

theorem ordinaryPairsValue :
    evaluate (ordinaryPairs n) (inputs types heads labels tupleBound variableBound prior opened) =
      Encodable.encode (cross (heads.map headNumber) prior) := by
  change evaluate NumericDependencyCross.cross
    (ofFn ![evaluate (convertedHeads n) (inputs types heads labels tupleBound variableBound prior opened),Encodable.encode prior]) = _
  rw [convertedHeadsValue,crossEncoding]

theorem ordinaryEncoding (h : HeadCode (Fin n)) (c : Code (Fin n)) :
    Encodable.encode (Code.ordinary h c) = Nat.pair 4 (Nat.pair (headNumber h) (Encodable.encode c)) := rfl

theorem ordinaryValue : evaluate (ordinary n) (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode ((cross heads prior).map (fun q => Code.ordinary q.1 q.2)) := by
  change evaluate (InternalListMap.map (tagPayload 4))
    (ofFn ![evaluate (ordinaryPairs n) (inputs types heads labels tupleBound variableBound prior opened)]) = _
  rw [ordinaryPairsValue]
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  rw [rawMapValue]
  simp only [cross,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def,
    tagValue,Encodable.encode_prod_val,Encodable.encode_nat,ordinaryEncoding]
  rfl

theorem labelRangeValue : evaluate labelRange (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode (List.range (labels+1)) := by
  change evaluate OriginalAscendingRange.range (ofFn ![labels+1]) = _
  exact OriginalAscendingRange.NativeProof.nativeRange _

theorem typeTuplesValue : evaluate typeTuples (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode (NumberedAuxiliaryEnumeration.typeLists types tupleBound) := by
  change evaluate OriginalTypeListsEnumeration.enumeration (ofFn ![tupleBound,Encodable.encode types]) = _
  exact OriginalTypeListsEnumeration.NativeProof.encodedValue types tupleBound

theorem numberedValue : evaluate (numbered n) (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode ((cross (List.range (labels+1))
      (cross heads (cross types (cross prior
        (cross (NumberedAuxiliaryEnumeration.typeLists types tupleBound) prior))))).map
      (fun q => Code.numbered q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)) := by
  change evaluate (OriginalEncodedNumberedEnumerationBranch.branch n)
    (ofFn ![evaluate labelRange (inputs types heads labels tupleBound variableBound prior opened),
      Encodable.encode heads,Encodable.encode types,Encodable.encode prior,
      evaluate typeTuples (inputs types heads labels tupleBound variableBound prior opened),Encodable.encode prior]) = _
  rw [labelRangeValue,typeTuplesValue,OriginalEncodedNumberedEnumerationBranch.NativeProof.nativeBranch]
  simp only [cross,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeHeadsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeHeadsProof
