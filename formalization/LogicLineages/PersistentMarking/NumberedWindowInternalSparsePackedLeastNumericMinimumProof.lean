module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericMinimumProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursion (listRec)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum minimumStep)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (stepValue)
open NumberedWindowInternalSparsePackedLeastTargets

private theorem foldValue (xs : List Nat) :
    xs.foldr (fun h r => evaluate minimumStep (h ::ᵥ r ::ᵥ nil)) 0 = encodeState xs.min? := by
  induction xs with
  | nil => rfl
  | cons h t ih => rw [List.foldr_cons, ih, stepValue, List.min?_cons]

theorem allInput : ExactAllInputScratchMinimum := by
  intro code
  change evaluate (listRec (constantZero 0) minimumStep)
    (code ::ᵥ (nil : List.Vector Nat 0)) = _
  rw [actualRawListRecursionEvaluation 0 (constantZero 0) minimumStep (nil : List.Vector Nat 0) code]
  exact foldValue ((decodeNumbers code).getD [])

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericMinimumProof
