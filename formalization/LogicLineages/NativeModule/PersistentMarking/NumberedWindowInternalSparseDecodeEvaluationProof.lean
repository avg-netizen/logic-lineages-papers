module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPairDecodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeEvaluationProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalSquareRootEvaluationProof (exactSquareRootEvaluation)
open InternalArithmeticProgramsEvaluationProof (vectorTwo exactMultiplicationEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeTargets
open NumberedWindowArithmeticPairDecodeProof (exactDecode exactNonPair)

private theorem squareValue (n : Nat) :
    evaluate rootSquare (n ::ᵥ nil) = Nat.sqrt n * Nat.sqrt n := by
  simp only [rootSquare,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactMultiplicationEvaluation,exactSquareRootEvaluation]

private theorem leftValue (n : Nat) :
    evaluate leftCandidate (n ::ᵥ nil) = n - Nat.sqrt n * Nat.sqrt n := by
  simp only [leftCandidate,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  change evaluate InternalEqualityTest.subtract (evaluate rootSquare (n ::ᵥ nil) ::ᵥ n ::ᵥ nil) = _
  rw [exactSubtractionEvaluation,squareValue]

private theorem rightValue (n : Nat) :
    evaluate rightCandidate (n ::ᵥ nil) = Nat.sqrt n - (n - Nat.sqrt n * Nat.sqrt n) := by
  simp only [rightCandidate,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactSubtractionEvaluation,exactSquareRootEvaluation,leftValue]

theorem candidates : CandidateValues := by
  intro n
  exact ⟨leftValue n,rightValue n⟩

private theorem gapValue (n : Nat) :
    evaluate gap (n ::ᵥ nil) = if Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n then 1 else 0 := by
  simp only [gap,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactLessThanEvaluation,exactSquareRootEvaluation,leftValue]

theorem guardValue : GuardValue := by
  intro n
  unfold good
  rw [evalBranch,gapValue]
  change (if (if Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n then 1 else 0) = (0 : Nat)
    then 1 else 0) = _
  by_cases h : n - Nat.sqrt n * Nat.sqrt n ≤ Nat.sqrt n
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

private theorem rootOfPair (x y : Nat) :
    Nat.sqrt (NumberedWindowPairAlgorithm.pair x y) = x+y := by
  let s := x+y
  symm
  apply Nat.eq_sqrt.mpr
  change s*s ≤ s*s+x ∧ s*s+x < (s+1)*(s+1)
  constructor
  · exact Nat.le_add_right _ _
  · apply Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right x y) (s*s))
    rw [Nat.mul_succ,Nat.succ_mul]
    omega

theorem allInputDecoder : AllInputDecoder := by
  intro n
  let s := Nat.sqrt n
  let r := n - s*s
  have hbound : s*s ≤ n := Nat.sqrt_le n
  unfold chosenDecode
  dsimp only
  rw [guardValue n,leftValue,rightValue]
  change (if (if r ≤ s then 1 else 0) = (1 : Nat) then some (r,s-r) else none) = _
  by_cases h : r ≤ s
  · have hp : NumberedWindowPairAlgorithm.pair r (s-r) = n := by
      unfold NumberedWindowPairAlgorithm.pair
      rw [Nat.add_sub_of_le h]
      exact Nat.add_sub_of_le hbound
    simp [h]
    exact ((exactDecode n r (s-r)).mpr hp).symm
  · have hd : NumberedWindowPairAlgorithm.decode n = none := by
      apply (exactNonPair n).mpr
      rintro ⟨x,y,hp⟩
      have hs : s = x+y := by
        change Nat.sqrt n = _
        rw [← hp]
        exact rootOfPair x y
      have hr : r = x := by
        change n-s*s = x
        rw [← hp,hs]
        simp [NumberedWindowArithmeticPair.pair]
      apply h
      rw [hs,hr]
      exact Nat.le_add_right _ _
    simp [h,hd]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeEvaluationProof
