module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof
  (vectorOne vectorThree exactPredecessorEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (mapped)
open NumberedWindowInternalDirectInsertedTargetsNumericProof (exact_OriginalRawInsertedTargetsNumeric)
open NumberedWindowInternalDirectSourcePartitionRawTargets (payloadAt)
open NumberedWindowInternalDirectRawSourceNumericProof
open NumberedWindowInternalDirectCoreNumericTargets (CountFit partition)
open NumberedWindowInternalDirectTargetPartitionRawTargets

private theorem projectionValue (t k a : Nat) :
    evaluate mapAt (t ::ᵥ k ::ᵥ a ::ᵥ nil) = encodeResult ((unpack a).bind mapped) := by
  unfold mapAt
  rw [evaluate,vectorOne]
  exact exact_OriginalRawInsertedTargetsNumeric a

private theorem readyValue (t k a : Nat) :
    evaluate mapReady (t ::ᵥ k ::ᵥ a ::ᵥ nil) = ((unpack a).bind mapped).isSome.toNat := by
  unfold mapReady
  rw [evalBranch,projectionValue]
  cases (unpack a).bind mapped with
  | none => rfl
  | some ls =>
    change (if numbersNumber ls + 1 = 0 then 0 else 1) = _
    rw [if_neg (Nat.succ_ne_zero _)]
    rfl

private theorem payloadValue (t k a : Nat) (ls : List Nat) (seen : (unpack a).bind mapped = some ls) :
    evaluate mapPayload (t ::ᵥ k ::ᵥ a ::ᵥ nil) = numbersNumber ls := by
  unfold mapPayload
  rw [evaluate,vectorOne]
  change evaluate ID1Completion.InternalEqualityTest.predecessor
    (evaluate mapAt (t ::ᵥ k ::ᵥ a ::ᵥ nil) ::ᵥ nil) = _
  rw [projectionValue,seen,exactPredecessorEvaluation]
  rfl

private theorem allValue (t k a : Nat) :
    evaluate allReady (t ::ᵥ k ::ᵥ a ::ᵥ nil) =
      ((unpack t).isSome && (unpack k).isSome && ((unpack a).bind mapped).isSome).toNat := by
  unfold allReady
  rw [conjunctionEvaluation,conjunctionEvaluation,exact_ParsedFlagNumeric,exact_ParsedFlagNumeric,readyValue]
  have bit (x y z : Bool) :
      (if x.toNat = 1 ∧ (if y.toNat = 1 ∧ z.toNat = 1 then 1 else 0) = 1 then 1 else 0) =
        (x && y && z).toNat := by
    cases x <;> cases y <;> cases z <;> rfl
  exact bit (unpack t).isSome (unpack k).isSome ((unpack a).bind mapped).isSome

/-- Compare exactly the newly inserted target fields, in the unchanged
order and with duplicates retained, at the original target partition. -/
theorem exact_RawTargetPartitionNumeric (count : Program 2) (fit : CountFit count) (t k a : Nat) :
    evaluate (rawTargetCheck count) (t ::ᵥ k ::ᵥ a ::ᵥ nil) =
      (partition (unpack t) (unpack k) ((unpack a).bind mapped)).toNat := by
  let tape := t ::ᵥ k ::ᵥ a ::ᵥ nil
  change evaluate (rawTargetCheck count) tape = _
  unfold rawTargetCheck
  rw [conjunctionEvaluation,allValue]
  unfold partition
  cases ht : unpack t <;> cases hk : unpack k <;> cases ha : (unpack a).bind mapped <;>
    simp only [Option.isSome,Bool.false_and,Bool.and_false,Bool.true_and,Bool.and_true,
      Bool.toNat,Bool.cond_false,Bool.cond_true,Nat.zero_ne_one,false_and,if_false,true_and]
  rename_i xs ys zs
  unfold decodeCall
  rw [evaluate,vectorThree]
  change (if evaluate (NumberedWindowInternalDirectSourcePartitionRawTargets.observePartition count)
    (evaluate (payloadAt 0) tape ::ᵥ evaluate (payloadAt 1) tape ::ᵥ evaluate mapPayload tape ::ᵥ nil) = 1
    then 1 else 0) = (decide (xs.Perm (ys ++ zs))).toNat
  rw [exact_ParsedPayloadSlotNumeric 0 tape xs ht,exact_ParsedPayloadSlotNumeric 1 tape ys hk,
    payloadValue t k a zs ha,exact_ObservePartitionNumeric count fit]
  cases decide (xs.Perm (ys ++ zs)) <;> rfl

#print axioms exact_RawTargetPartitionNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetNumericProof
