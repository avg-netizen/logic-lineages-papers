module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedHeadCodecPrimrec
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem chooseEvaluation (tag : Nat) (yes no : Program 1) (v : List.Vector Nat 1) :
    evaluate (choose tag yes no) v =
      if (Nat.unpair (v.get 0)).1 = tag then evaluate yes v else evaluate no v := by
  simp only [choose,evalBranch,sameOfEvaluation,leftEvaluation,constantEvaluation]
  split_ifs <;> simp_all

theorem payloadEvaluation (tag raw : Nat) :
    evaluate (atPayload tag) (List.Vector.ofFn ![raw]) =
    evaluate (branchCode tag) (List.Vector.ofFn ![(Nat.unpair raw).2]) := by
  rw [atPayload,unaryCompositionEvaluation,rightEvaluation]
  rfl

theorem projectionOne (x : Nat) : evaluate (.projection 0 : Program 1) (List.Vector.ofFn ![x]) = x := rfl

theorem branchValue0 (x : Nat) : evaluate (branchCode 0) (List.Vector.ofFn ![x]) = 0 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem branchValue1 (x : Nat) : evaluate (branchCode 1) (List.Vector.ofFn ![x]) = 2 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem branchValue2 (x : Nat) : evaluate (branchCode 2) (List.Vector.ofFn ![x]) = (x+x)+(x+x)+1 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem branchValue3 (x : Nat) : evaluate (branchCode 3) (List.Vector.ofFn ![x]) = ((x+x)+(x+x)+1)+((x+x)+(x+x)+1)+1 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem branchValue4 (x : Nat) : evaluate (branchCode 4) (List.Vector.ofFn ![x]) = (((x+x)+(x+x)+1)+((x+x)+(x+x)+1)+1)+(((x+x)+(x+x)+1)+((x+x)+(x+x)+1)+1)+1 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem branchValue5 (x : Nat) : evaluate (branchCode 5) (List.Vector.ofFn ![x]) = (((x+x+1)+(x+x+1)+1)+((x+x+1)+(x+x+1)+1)+1)+(((x+x+1)+(x+x+1)+1)+((x+x+1)+(x+x+1)+1)+1)+1 := by
  simp only [branchCode,sumLeft,sumRight,succOfEvaluation,addOfEvaluation,constantEvaluation,projectionOne]

theorem nativeHeadEncoding : Targets.NativeHeadEncoding := by
  intro n h
  change evaluate encodeHead (List.Vector.ofFn ![headNumber h]) = Encodable.encode ((headEquiv n) h)
  cases h <;>
    simp [encodeHead,chooseEvaluation,headNumber,Nat.unpair_pair,payloadEvaluation,
      branchValue0,branchValue1,branchValue2,branchValue3,branchValue4,branchValue5,
      headEquiv,Encodable.encode_inl,Encodable.encode_inr,Encodable.encode_true,
      Encodable.encode_false,Encodable.encode_prod_val] <;> omega

theorem nativeTypeListEncoding : Targets.NativeTypeListEncoding := by
  intro ts
  change typesNumber ts = Encodable.encodeList ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change 1 + Nat.pair (typeNumber t) (typesNumber ts) =
      Nat.succ (Nat.pair (typeNumber t) (Encodable.encodeList ts))
    rw [ih,Nat.add_comm]
    rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
