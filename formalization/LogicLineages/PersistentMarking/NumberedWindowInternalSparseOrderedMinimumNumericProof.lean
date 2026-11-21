module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (exactPredecessorEvaluation)
open InternalRawListRecursion (listRec)
open InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparseOrderedMinimum
open NumberedWindowInternalSparseOrderedMinimumTargets
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (stepValue unaryValue)

private theorem foldValue (xs : List Nat) :
    xs.foldr (fun h r => evaluate minimumStep (h ::ᵥ r ::ᵥ nil)) 0 = encodeState xs.min? := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
    rw [List.foldr_cons,ih,stepValue,List.min?_cons]

private theorem scratch (xs : List Nat) :
    evaluate scratchMinimum (numbersNumber xs ::ᵥ nil) = encodeState xs.min? := by
  change evaluate (listRec (constantZero 0) minimumStep)
    (numbersNumber xs ::ᵥ (nil : List.Vector Nat 0)) = _
  rw [actualRawListRecursionEvaluation 0 (constantZero 0) minimumStep
    (nil : List.Vector Nat 0) (numbersNumber xs),numbersRoundTrip xs]
  exact foldValue xs

theorem allInput : ExactAllInputOrderedPoolMinimum := by
  intro q
  cases parsed : unpack q with
  | none =>
    rw [orderedPoolMinimum,evalBranch,exact_ActualEncodedOutput q,parsed] <;> rfl
  | some xs =>
    have code : evaluate decodedScratch (q ::ᵥ nil) = numbersNumber xs := by
      rw [decodedScratch,unaryValue,exactPredecessorEvaluation,exact_ActualEncodedOutput q,parsed] <;> rfl
    have result : evaluate parsedMinimum (q ::ᵥ nil) = encodeState xs.min? := by
      rw [parsedMinimum,unaryValue,code]
      exact scratch xs
    rw [orderedPoolMinimum,evalBranch,exact_ActualEncodedOutput q,parsed,result]
    change (if numbersNumber xs + 1 = 0 then 0 else encodeState xs.min?) = encodeState xs.min?
    exact if_neg (Nat.succ_ne_zero (numbersNumber xs))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericProof
