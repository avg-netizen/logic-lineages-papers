module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeNodesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof

theorem rankValue (v : List.Vector Nat 2) : evaluate R v = (Nat.unpair (v.get 0)).2 := by
  simp only [R,rightOfEvaluation,projectionEvaluation]
theorem boundValue (v : List.Vector Nat 2) : evaluate bound v = (Nat.unpair (v.get 0)).1 := by
  simp only [bound,leftOfEvaluation,projectionEvaluation]
theorem previousValue (v : List.Vector Nat 2) : evaluate previousFuel v = (Nat.unpair (v.get 0)).2 - 1 := by
  change evaluate InternalEqualityTest.predecessor (ofFn ![evaluate R v]) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne,InternalEqualityTestEvaluationProof.exactPredecessorEvaluation,rankValue]
  rfl

theorem priorValue (v : List.Vector Nat 2) : evaluate priorNode v =
    Nat.pair (Nat.unpair (v.get 0)).1 ((Nat.unpair (v.get 0)).2 - 1) := by
  simp only [priorNode,pairOfEvaluation,boundValue,previousValue]
theorem openedValue (v : List.Vector Nat 2) : evaluate openedNode v =
    Nat.pair ((Nat.unpair (v.get 0)).1 + 1) ((Nat.unpair (v.get 0)).2 - 1) := by
  rw [openedNode,pairOfEvaluation,previousValue]
  change Nat.pair (evaluate bound v + 1) ((Nat.unpair (v.get 0)).2 - 1) = _
  rw [boundValue]

theorem consValue (a b : Nat) : evaluate InternalListCodec.consCode (ofFn ![a,b]) = 1 + Nat.pair a b := by
  rw [InternalEqualityTestEvaluationProof.vectorTwo,InternalListCodecEvaluationProof.consEvaluation]
  rfl

theorem positiveValue (v : List.Vector Nat 2) : evaluate positiveDependencies v =
    1 + Nat.pair (Nat.pair (Nat.unpair (v.get 0)).1 ((Nat.unpair (v.get 0)).2 - 1))
      (1 + Nat.pair (Nat.pair ((Nat.unpair (v.get 0)).1 + 1) ((Nat.unpair (v.get 0)).2 - 1)) 0) := by
  change evaluate InternalListCodec.consCode
    (ofFn ![evaluate priorNode v,evaluate InternalListCodec.consCode (ofFn ![evaluate openedNode v,0])]) = _
  rw [consValue,consValue,priorValue,openedValue]

theorem nativeRank : Targets.NativeRank := rankValue

theorem nativeDependencies : Targets.NativeDependencies := by
  intro v
  rw [D,evalBranch,rankValue,positiveValue]
  change (if (Nat.unpair (v.get 0)).2 = 0 then 0 else
    1 + Nat.pair (Nat.pair (Nat.unpair (v.get 0)).1 ((Nat.unpair (v.get 0)).2 - 1))
      (1 + Nat.pair (Nat.pair ((Nat.unpair (v.get 0)).1 + 1) ((Nat.unpair (v.get 0)).2 - 1)) 0)) = _
  cases hf : (Nat.unpair (v.get 0)).2 with
  | zero => simp only [hf,ite_true,NumberedCodeEnumerationPrimrecProof.dependencies,Encodable.encode_list_nil]
  | succ fuel =>
    simp only [hf,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
      NumberedCodeEnumerationPrimrecProof.dependencies,Encodable.encode_list_cons,Encodable.encode_list_nil,
      Encodable.encode_prod_val,Encodable.encode_nat,Nat.succ_eq_add_one,Nat.add_comm]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeNodesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeNodesProof
