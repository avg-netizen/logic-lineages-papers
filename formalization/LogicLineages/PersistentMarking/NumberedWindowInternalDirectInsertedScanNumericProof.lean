module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScan
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalDirectInsertedScanTargets
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow expected parseRemoved poolReady poolCode)
open NumberedWindowInternalDirectInsertedRow (exactNumericInsertedRow)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne chooseBranch zeroAt literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (bothEvaluation compositeOne compositeTwo branchEvaluation zeroEvaluation literalEvaluation predEvaluation)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)

private theorem conValue {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs =
      (if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0) :=
  bothEvaluation p q xs

private theorem rowValue (r : Program 3) (row prev removed : Nat) :
    evaluate (rowAt r) (row ::ᵥ prev ::ᵥ removed ::ᵥ nil) =
      (expected r removed row).toNat := by
  change evaluate (.composition (insertedRow r)
    (Fin.cons (.projection 2) (Fin.cons (.projection 0) Fin.elim0))) _ = _
  rw [compositeTwo (insertedRow r) (.projection 2) (.projection 0)]
  exact exactNumericInsertedRow r removed row

private theorem stepValue (r : Program 3) (row prev removed : Nat) :
    evaluate (scanStep r) (row ::ᵥ prev ::ᵥ removed ::ᵥ nil) =
      if expected r removed row = true ∧ prev = 1 then 1 else 0 := by
  change evaluate (conjunction (rowAt r) (.projection 1)) _ = _
  rw [conValue,rowValue]
  change (if (expected r removed row).toNat = 1 ∧ prev = 1 then 1 else 0) = _
  cases expected r removed row <;> simp

private theorem headFold (r : Program 3) (removed : Nat) (rows : List Nat) :
    rows.foldr (fun h prev => evaluate (scanStep r) (h ::ᵥ prev ::ᵥ removed ::ᵥ nil))
      (evaluate scanBase (removed ::ᵥ nil)) = (rows.all (expected r removed)).toNat := by
  induction rows with
  | nil => exact literalEvaluation 1 1 _
  | cons h rows ih =>
    rw [List.foldr_cons,stepValue,ih,List.all_cons]
    cases expected r removed h <;> cases rows.all (expected r removed) <;> simp [Bool.toNat]

private theorem loopValue (r : Program 3) (removed : Nat) (rows : List Nat) :
    evaluate (scanLoop r) (numbersNumber rows ::ᵥ removed ::ᵥ nil) =
      (rows.all (expected r removed)).toNat := by
  have h := actualRawListRecursionEvaluation 1 scanBase (scanStep r) (removed ::ᵥ nil) (numbersNumber rows)
  rw [numbersRoundTrip] at h
  exact h.trans (headFold r removed rows)

private theorem parseValue (inserted removed : Nat) :
    evaluate parseRemoved (inserted ::ᵥ removed ::ᵥ nil) = encodeResult (unpack inserted) := by
  change evaluate (.composition parser (Fin.cons (.projection 0) Fin.elim0)) _ = _
  rw [compositeOne parser (.projection 0)]
  exact exact_ActualEncodedOutput inserted

private theorem readyValue (inserted removed : Nat) :
    evaluate poolReady (inserted ::ᵥ removed ::ᵥ nil) = if (unpack inserted).isSome then 1 else 0 := by
  change evaluate (chooseBranch parseRemoved (zeroAt 2) (literal 2 1)) _ = _
  rw [branchEvaluation,parseValue,zeroEvaluation,literalEvaluation]
  cases unpack inserted <;> rfl

private theorem poolValue (inserted removed : Nat) (xs : List Nat) (h : unpack inserted = some xs) :
    evaluate poolCode (inserted ::ᵥ removed ::ᵥ nil) = numbersNumber xs := by
  change evaluate (.composition predOne (Fin.cons parseRemoved Fin.elim0)) _ = _
  rw [compositeOne predOne parseRemoved,parseValue,h]
  exact predEvaluation (numbersNumber xs + 1)

private theorem scanAtValue (r : Program 3) (inserted removed : Nat) (xs : List Nat)
    (h : unpack inserted = some xs) :
    evaluate (scanAt r) (inserted ::ᵥ removed ::ᵥ nil) = (xs.all (expected r removed)).toNat := by
  change evaluate (.composition (scanLoop r) (Fin.cons poolCode (Fin.cons (.projection 1) Fin.elim0))) _ = _
  rw [compositeTwo (scanLoop r) poolCode (.projection 1),poolValue inserted removed xs h]
  exact loopValue r removed xs

theorem exactNumericScan : ExactNumericScan := by
  intro r inserted removed
  unfold scan
  rw [conValue,readyValue]
  cases hu : unpack inserted with
  | none => simp
  | some xs =>
    rw [scanAtValue r inserted removed xs hu]
    simp only [Option.any]
    cases xs.all (expected r removed) <;> simp [Bool.toNat]

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScan
