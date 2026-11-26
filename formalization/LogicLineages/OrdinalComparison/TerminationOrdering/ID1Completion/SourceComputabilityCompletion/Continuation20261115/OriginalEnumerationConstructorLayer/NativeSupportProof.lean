module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)

theorem tagValue (tag : Nat) (v : List.Vector Nat 1) : evaluate (tagPayload tag) v = Nat.pair tag (v.get 0) := by
  simp only [tagPayload,pairOfEvaluation,constantEvaluation,projectionEvaluation]

theorem rawMapValue (F : Program 1) (xs : List Nat) :
    evaluate (InternalListMap.map F) (ofFn ![numbersNumber xs]) =
      numbersNumber (xs.map (fun x => evaluate F (ofFn ![x]))) := by
  have hm := InternalListMapEvaluationProof.actualRawListMapEvaluation 0 F nil (numbersNumber xs)
  change evaluate (InternalListMap.map F) (ofFn ![numbersNumber xs]) = _ at hm
  rw [hm,numbersRoundTrip]
  rfl

theorem mapEncoding {A B : Type} [Encodable A] [Encodable B]
    (F : Program 1) (f : A → B)
    (hf : ∀ x, evaluate F (ofFn ![Encodable.encode x]) = Encodable.encode (f x))
    (xs : List A) :
    evaluate (InternalListMap.map F) (ofFn ![Encodable.encode xs]) = Encodable.encode (xs.map f) := by
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  rw [rawMapValue,List.map_map,List.map_map]
  apply congrArg numbersNumber
  apply congrArg (fun g => xs.map g)
  funext x
  exact hf x

theorem crossEncoding {A B : Type} [Encodable A] [Encodable B] (xs : List A) (ys : List B) :
    evaluate NumericDependencyCross.cross (ofFn ![Encodable.encode xs,Encodable.encode ys]) =
      Encodable.encode (NumberedCodeEnumerationPrimrecSupportProof.cross xs ys) := by
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  rw [NumericDependencyCross.NativeProof.crossValue]
  simp only [NumberedCodeEnumerationPrimrecSupportProof.cross,List.flatMap_map,List.map_flatMap,List.map_map,
    Function.comp_def,Encodable.encode_prod_val]

theorem appendEncoding {A : Type} [Encodable A] (xs ys : List A) :
    evaluate InternalApplicationValidityStackAppend.append (ofFn ![Encodable.encode xs,Encodable.encode ys]) =
      Encodable.encode (xs ++ ys) := by
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding,List.map_append]
  exact Continuation20261114.OriginalSourceHeads.RawProof.appendValue _ _

theorem joinEncoding {A : Type} [Encodable A] (a b : Program 7) (v : List.Vector Nat 7)
    (xs ys : List A) (ha : evaluate a v = Encodable.encode xs) (hb : evaluate b v = Encodable.encode ys) :
    evaluate (join a b) v = Encodable.encode (xs ++ ys) := by
  change evaluate InternalApplicationValidityStackAppend.append (ofFn ![evaluate a v,evaluate b v]) = _
  rw [ha,hb,appendEncoding]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeSupportProof
