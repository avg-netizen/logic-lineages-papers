module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof
  (vectorOne vectorTwo vectorThree exactPredecessorEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectCoreNumericTargets (CountFit partition)
open NumberedWindowInternalFunctionalRawUnionNumericProof (exact_ScratchAppendOnLists)

theorem exact_ParserSlotNumeric (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parserAt i) xs = encodeResult (unpack (xs.get i)) := by
  unfold parserAt
  rw [evaluate,vectorOne]
  exact exact_ActualEncodedOutput (xs.get i)

theorem exact_ParsedFlagNumeric (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parsedAt i) xs = (unpack (xs.get i)).isSome.toNat := by
  unfold parsedAt
  rw [evalBranch,exact_ParserSlotNumeric]
  cases unpack (xs.get i) with
  | none => rfl
  | some list =>
    change (if numbersNumber list + 1 = 0 then 0 else 1) = _
    rw [if_neg (Nat.succ_ne_zero _)]
    rfl

theorem exact_ParsedPayloadSlotNumeric (i : Fin 3) (xs : List.Vector Nat 3) (L : List Nat)
    (found : unpack (xs.get i) = some L) :
    evaluate (payloadAt i) xs = numbersNumber L := by
  unfold payloadAt
  rw [evaluate,vectorOne]
  change evaluate ID1Completion.InternalEqualityTest.predecessor
    (evaluate (parserAt i) xs ::ᵥ nil) = _
  rw [exact_ParserSlotNumeric,found,exactPredecessorEvaluation]
  simp [encodeResult]

private theorem readAll (xs : List.Vector Nat 3) :
    evaluate parsedAll xs =
      ((unpack (xs.get 0)).isSome && (unpack (xs.get 1)).isSome && (unpack (xs.get 2)).isSome).toNat := by
  unfold parsedAll
  rw [conjunctionEvaluation,conjunctionEvaluation,exact_ParsedFlagNumeric,
    exact_ParsedFlagNumeric,exact_ParsedFlagNumeric]
  cases unpack (xs.get 0) <;> cases unpack (xs.get 1) <;> cases unpack (xs.get 2) <;> rfl

/-- The exact same raw decoding and scratch values at all three physical
slots. A malformed input is rejected regardless of the selected core. -/
theorem exact_OriginalRawSourceCheckNumeric (core : Program 3) (a b c : Nat) :
    evaluate (rawSourceCheck core) (a ::ᵥ b ::ᵥ c ::ᵥ nil) =
      match unpack a, unpack b, unpack c with
      | some xs,some ys,some zs =>
        if evaluate core (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber zs ::ᵥ nil) = 1
        then 1 else 0
      | _,_,_ => 0 := by
  let tape := a ::ᵥ b ::ᵥ c ::ᵥ nil
  change evaluate (rawSourceCheck core) tape = _
  unfold rawSourceCheck
  rw [conjunctionEvaluation,readAll]
  change (if ((unpack a).isSome && (unpack b).isSome && (unpack c).isSome).toNat = 1 ∧
     evaluate (decodedCall core) tape = 1 then 1 else 0) = _
  cases ha : unpack a <;> cases hb : unpack b <;> cases hc : unpack c <;>
    simp only [ha,hb,hc,Option.isSome,Bool.false_and,Bool.and_false,Bool.true_and,Bool.and_true,
      Bool.toNat,Bool.cond_false,Bool.cond_true,Nat.zero_ne_one,false_and,if_false,true_and]
  rename_i xs ys zs
  unfold decodedCall
  rw [evaluate,vectorThree]
  change (if evaluate core (evaluate (payloadAt 0) tape ::ᵥ
    evaluate (payloadAt 1) tape ::ᵥ evaluate (payloadAt 2) tape ::ᵥ nil) = 1 then 1 else 0) = _
  rw [exact_ParsedPayloadSlotNumeric 0 tape xs ha,exact_ParsedPayloadSlotNumeric 1 tape ys hb,
    exact_ParsedPayloadSlotNumeric 2 tape zs hc]

theorem exact_ObservePartitionNumeric (count : Program 2) (fitted : CountFit count)
    (xs ys zs : List Nat) :
    evaluate (observePartition count)
      (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber zs ::ᵥ nil) =
    (decide (xs.Perm (ys ++ zs))).toNat := by
  unfold observePartition
  rw [evaluate,vectorTwo]
  change evaluate count (numbersNumber xs ::ᵥ evaluate appendKeptRemoved
    (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber zs ::ᵥ nil) ::ᵥ nil) = _
  have writes : evaluate appendKeptRemoved (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber zs ::ᵥ nil)
      = numbersNumber (ys ++ zs) := by
    unfold appendKeptRemoved
    rw [evaluate,vectorTwo]
    exact exact_ScratchAppendOnLists ys zs
  rw [writes,fitted xs (ys ++ zs)]

theorem exact_RawSourcePartitionNumeric (count : Program 2) (fitted : CountFit count) (s k r : Nat) :
    evaluate (rawSourceCheck (observePartition count)) (s ::ᵥ k ::ᵥ r ::ᵥ nil) =
      (partition (unpack s) (unpack k) (unpack r)).toNat := by
  rw [exact_OriginalRawSourceCheckNumeric]
  unfold partition
  cases unpack s <;> cases unpack k <;> cases unpack r <;> try rfl
  rename_i xs ys zs
  change (if evaluate (observePartition count)
      (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ numbersNumber zs ::ᵥ nil) = 1 then 1 else 0) =
    (decide (xs.Perm (ys ++ zs))).toNat
  rw [exact_ObservePartitionNumeric count fitted]
  cases decide (xs.Perm (ys ++ zs)) <;> rfl

#print axioms exact_OriginalRawSourceCheckNumeric
#print axioms exact_ObservePartitionNumeric
#print axioms exact_RawSourcePartitionNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceNumericProof
