module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow expected poolCode poolReady)
open NumberedWindowInternalDirectInsertedRowNumericProof
open NumberedWindowInternalDirectInsertedScanTargets

private theorem rowValue (r : Program 3) (row prev removed : Nat) :
    evaluate (rowAt r) (row ::ᵥ prev ::ᵥ removed ::ᵥ nil) = (expected r removed row).toNat := by
  unfold rowAt
  rw [evaluate,vectorTwo]
  exact exact_OriginalInsertedRowNumeric r removed row

private theorem stepValue (r : Program 3) (row prev removed : Nat) :
    evaluate (scanStep r) (row ::ᵥ prev ::ᵥ removed ::ᵥ nil) =
      if (expected r removed row).toNat = 1 ∧ prev = 1 then 1 else 0 := by
  unfold scanStep
  rw [conjunctionEvaluation,rowValue]
  rfl

theorem exact_OriginalScanLoopNumeric (r : Program 3) (rows : List Nat) (removed : Nat) :
    evaluate (scanLoop r) (numbersNumber rows ::ᵥ removed ::ᵥ nil) =
      (rows.all (expected r removed)).toNat := by
  unfold scanLoop
  rw [actualRawListRecursionEvaluation,numbersRoundTrip]
  change rows.foldr (fun a b => evaluate (scanStep r) (a ::ᵥ b ::ᵥ removed ::ᵥ nil))
    (evaluate scanBase (removed ::ᵥ nil)) = _
  have b : evaluate scanBase (removed ::ᵥ nil) = 1 := literalEvaluation 1 1 _
  rw [b]
  induction rows with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldr_cons,ih,stepValue,List.all_cons]
    cases expected r removed a <;> cases as.all (expected r removed) <;> rfl

theorem exact_OriginalInsertedScanNumeric : ExactNumericScan := by
  intro r added removed
  unfold scan
  rw [conjunctionEvaluation,exact_InsertedPoolReadyNumeric]
  cases e : unpack added with
  | none => rfl
  | some rows =>
    have good : evaluate (scanAt r) (added ::ᵥ removed ::ᵥ nil) =
        (rows.all (expected r removed)).toNat := by
      unfold scanAt
      rw [evaluate,vectorTwo]
      change evaluate (scanLoop r)
        (evaluate poolCode (added ::ᵥ removed ::ᵥ nil) ::ᵥ removed ::ᵥ nil) = _
      rw [exact_InsertedPoolCodeNumeric added removed rows e,exact_OriginalScanLoopNumeric]
    rw [good]
    change (if (1 : Nat) = 1 ∧ (rows.all (expected r removed)).toNat = 1 then 1 else 0) =
      (rows.all (expected r removed)).toNat
    cases rows.all (expected r removed) <;> rfl

#print axioms exact_OriginalScanLoopNumeric
#print axioms exact_OriginalInsertedScanNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanNumericProof
