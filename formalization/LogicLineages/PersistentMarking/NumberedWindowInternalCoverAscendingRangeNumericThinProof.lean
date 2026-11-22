module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeNumericThinProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalCoverAscendingRangeTargets

private theorem appendFold (xs ys : List Nat) :
    xs.foldr (fun k a => 1 + Nat.pair k a) (numbersNumber ys) =
      numbersNumber (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

private theorem encodeAppend (xs ys : List Nat) :
    evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) =
      numbersNumber (xs ++ ys) := by
  have h := actualRawListRecursionEvaluation
    1 (.projection 0) appendStep (numbersNumber ys ::ᵥ nil) (numbersNumber xs)
  change evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) = _ at h
  rw [h,numbersRoundTrip]
  have hs (k a : Nat) :
      evaluate appendStep (k ::ᵥ a ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair k a := by
    exact consEvaluation k a
  simp only [hs]
  exact appendFold xs ys

private theorem singletonValue (i previous : Nat) :
    evaluate singleton (i ::ᵥ previous ::ᵥ nil) = numbersNumber [i] := by
  change evaluate consCode (ofFn ![i,0]) = _
  rw [vectorTwo,consEvaluation]
  rfl

private theorem stepValue (i : Nat) (xs : List Nat) :
    evaluate rangeStep (i ::ᵥ numbersNumber xs ::ᵥ nil) = numbersNumber (xs ++ [i]) := by
  change evaluate append
    (ofFn ![numbersNumber xs,evaluate singleton (i ::ᵥ numbersNumber xs ::ᵥ nil)]) = _
  rw [singletonValue,vectorTwo]
  change evaluate append (numbersNumber xs ::ᵥ numbersNumber [i] ::ᵥ nil) = _
  exact encodeAppend xs [i]

theorem exact_CoverAscendingRangeValue : ExactCoverAscendingRangeValue := by
  intro bound
  change Nat.rec (motive := fun _ => Nat) 0
    (fun i prev => evaluate rangeStep (i ::ᵥ prev ::ᵥ nil)) bound = _
  induction bound with
  | zero => rfl
  | succ n ih =>
    change evaluate rangeStep (n ::ᵥ Nat.rec (motive := fun _ => Nat) 0
      (fun i prev => evaluate rangeStep (i ::ᵥ prev ::ᵥ nil)) n ::ᵥ nil) = _
    rw [ih,stepValue,List.range_succ]

#print axioms exact_CoverAscendingRangeValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeNumericThinProof
