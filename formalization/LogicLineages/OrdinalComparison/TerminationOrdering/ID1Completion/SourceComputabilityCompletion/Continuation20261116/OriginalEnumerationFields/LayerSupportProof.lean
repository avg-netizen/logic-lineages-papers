module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RecombinationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne)
open Continuation20261115
open TwoSol20261113.CalibratedPrimary MembershipNativeProof
open SourceProof ListNativeProof

def convertedList (n raw : Nat) : List Nat := ((decodeNumbers raw).getD []).map (fun h =>
  ((Encodable.decode (α := NumberedAuxiliaryCoding.HeadCode (Fin n)) h).map
    NumberedLeastCodeRepresentative.headNumber).getD 0)

theorem typeMemberValue (ty : Program 3) (v : List.Vector Nat 3) :
    evaluate (typeMember ty) v =
      (decide (evaluate ty v ∈ (decodeNumbers (evaluate types v)).getD [])).toNat := by
  rw [typeMember,binaryCompositionEvaluation,actualContainsNative]

theorem headMemberValue (n : Nat) (h : Program 3) (v : List.Vector Nat 3) :
    evaluate (headMember n h) v =
      (decide (evaluate h v ∈ convertedList n (evaluate heads v))).toNat := by
  rw [headMember,binaryCompositionEvaluation]
  change evaluate Membership.contains
    (ofFn ![evaluate (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (ofFn ![evaluate heads v]),evaluate h v]) = _
  rw [convertedHeadsValue,actualContainsNative,numbersRoundTrip]
  rfl

theorem headNumbers (xs : List Nat) :
    evaluate InternalListCodec.headCode (ofFn ![numbersNumber xs]) = xs[0]?.getD 0 := by
  rw [vectorOne,InternalListCodecEvaluationProof.headEvaluation]
  cases xs <;> simp [numbersNumber,Nat.add_comm,Nat.unpair_pair]

theorem tailNumbers (xs : List Nat) :
    evaluate InternalListCodec.tailCode (ofFn ![numbersNumber xs]) = numbersNumber xs.tail := by
  rw [vectorOne,InternalListCodecEvaluationProof.tailEvaluation]
  cases xs <;> simp [numbersNumber,Nat.add_comm,Nat.unpair_pair]

theorem firstAnswerValue (key param : Nat) (xs : List Nat) :
    evaluate firstAnswer (ofFn ![key,numbersNumber xs,param]) = xs[0]?.getD 0 := by
  change evaluate InternalListCodec.headCode (ofFn ![numbersNumber xs]) = _
  exact headNumbers xs

theorem secondAnswerValue (key param : Nat) (xs : List Nat) :
    evaluate secondAnswer (ofFn ![key,numbersNumber xs,param]) = xs[1]?.getD 0 := by
  change evaluate InternalListCodec.headCode (ofFn ![evaluate InternalListCodec.tailCode (ofFn ![numbersNumber xs])]) = _
  rw [tailNumbers,headNumbers]
  cases xs <;> rfl

theorem typesNumberList (ts : List Source.Ty) :
    NumberedLeastCodeRepresentative.typesNumber ts = numbersNumber (ts.map NumberedLeastCodeRepresentative.typeNumber) := by
  induction ts with
  | nil => rfl
  | cons ty ts ih => simp only [NumberedLeastCodeRepresentative.typesNumber,List.map_cons,numbersNumber,ih]

theorem typesLength (ts : List Source.Ty) :
    evaluate OriginalContextInsertion.length (ofFn ![NumberedLeastCodeRepresentative.typesNumber ts]) = ts.length := by
  rw [typesNumberList,vectorOne,Matrix.cons_val_zero,OriginalContextInsertionCalibrationProof.lengthNumbers,List.length_map]

theorem typesAll (ts : List Source.Ty) (allowed : Nat) :
    evaluate allTypes (ofFn ![NumberedLeastCodeRepresentative.typesNumber ts,allowed]) =
      (ts.all (fun t => decide (NumberedLeastCodeRepresentative.typeNumber t ∈ (decodeNumbers allowed).getD []))).toNat := by
  rw [allTypesValue,typesNumberList,numbersRoundTrip]
  simp only [Option.getD_some,List.all_map]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
