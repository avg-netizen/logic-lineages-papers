module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHeadClassNumber NumberedLeastCodeRepresentative
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalCanonicalFixedWindowVertexDispatchEvaluationProof (constantEvaluation)
open InternalEqualityTestEvaluationProof
open InternalAcceptanceCalibrationProof

theorem tagEvaluation (n raw : Nat) : evaluate (tagIs n) (raw ::ᵥ nil) =
    if (Nat.unpair raw).1 = n then 1 else 0 := by
  unfold tagIs
  change evaluate InternalEqualityTest.equalityTest (ofFn fun i : Fin 2 =>
    evaluate ((![InternalUnpair.left,InternalCanonicalFixedWindowVertexDispatch.constant 1 n] : Fin 2 → Program 1) i) (raw ::ᵥ nil)) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate InternalUnpair.left (raw ::ᵥ nil) ::ᵥ evaluate (InternalCanonicalFixedWindowVertexDispatch.constant 1 n) (raw ::ᵥ nil) ::ᵥ nil) = _
  rw [leftEvaluation,constantEvaluation,exactEqualityEvaluation]
  rfl

theorem classEvaluation (tag payload : Nat) :
    evaluate classNumber (Nat.pair tag payload ::ᵥ nil) =
      if tag = 4 then 1 else if tag = 5 then payload+2 else 0 := by
  unfold classNumber
  rw [evalBranch,evalBranch,tagEvaluation,tagEvaluation]
  simp only [Nat.unpair_pair]
  have hz : evaluate (InternalAcceptance.constantZero 1) (Nat.pair tag payload ::ᵥ nil) = 0 := rfl
  have ho : evaluate (InternalLessThan.constantOne 1) (Nat.pair tag payload ::ᵥ nil) = 1 := rfl
  have hr : evaluate (.composition .succ (fun _ : Fin 1 => .composition .succ (fun _ : Fin 1 => InternalUnpair.right)))
      (Nat.pair tag payload ::ᵥ nil) = payload+2 := by
    change Nat.succ (Nat.succ (evaluate InternalUnpair.right (Nat.pair tag payload ::ᵥ nil))) = _
    rw [rightEvaluation]
    simp
  rw [hz,ho,hr]
  by_cases h4 : tag=4 <;> by_cases h5 : tag=5 <;> simp [h4,h5]

theorem nativeCalibration : OriginalHeadClassNumberTargets.NativeCalibration := by
  intro n h
  cases h <;> simp only [headNumber,classEvaluation,NumberedExchangeGuardsPrimrecProof.headClassNumber] <;> simp [Nat.add_comm]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberNativeProof
