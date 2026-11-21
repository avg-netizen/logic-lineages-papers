module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorTwo exactEqualityEvaluation)
open InternalRawListRecursion (listRec)
open InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparseScratchMembership
open NumberedWindowInternalSparseScratchMembershipTargets

private theorem stepValue (h previous k : Nat) :
    evaluate memberStep (h ::ᵥ previous ::ᵥ k ::ᵥ nil) = if h = k then 1 else previous := by
  have matchValue : evaluate headMatches (h ::ᵥ previous ::ᵥ k ::ᵥ nil) = if h = k then 1 else 0 := by
    change evaluate equalityTest (List.Vector.ofFn ![h,k]) = _
    rw [vectorTwo]
    exact exactEqualityEvaluation h k
  rw [memberStep,evalBranch,matchValue]
  by_cases eq : h = k
  · simp only [eq,ite_true,Nat.one_ne_zero,ite_false] <;> rfl
  · simp only [eq,ite_false,ite_true] <;> rfl

private theorem foldBit (pool : List Nat) (candidate : Nat) :
    pool.foldr (fun h r => evaluate memberStep (h ::ᵥ r ::ᵥ candidate ::ᵥ nil)) 0 =
      (pool.any (fun h => h == candidate)).toNat := by
  induction pool with
  | nil => rfl
  | cons h tail ih =>
    rw [List.foldr_cons,ih,stepValue,List.any_cons]
    cases matched : h == candidate with
    | false =>
      have opposite : h ≠ candidate := by
        intro hEq
        subst h
        simp at matched
      rw [if_neg opposite] <;> rfl
    | true => rw [if_pos (eq_of_beq matched)] <;> rfl

theorem allInput : ExactAllInputScratchMembership := by
  intro code candidate
  change evaluate (listRec memberBase memberStep) (code ::ᵥ candidate ::ᵥ nil) = _
  rw [actualRawListRecursionEvaluation 1 memberBase memberStep (candidate ::ᵥ nil) code]
  cases decoded : decodeNumbers code with
  | none => rfl
  | some pool => exact foldBit pool candidate

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericProof
