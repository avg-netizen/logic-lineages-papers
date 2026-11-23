module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison (permutation)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof (numericPermutation)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof (appendEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (chooseBranch zeroAt predOne literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo compositeThree branchEvaluation zeroEvaluation literalEvaluation predEvaluation
   bothEvaluation vectorTwo)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalDirectSourcePartitionTargets NumberedWindowInternalDirectSourcePartitionRawTargets

private theorem parserValue (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parserAt i) xs = encodeResult (unpack (xs.get i)) := by
  unfold parserAt
  rw [compositeOne]
  exact exact_ActualEncodedOutput (xs.get i)

private theorem readyValue (i : Fin 3) (xs : List.Vector Nat 3) :
    evaluate (parsedAt i) xs = (unpack (xs.get i)).isSome.toNat := by
  change evaluate (chooseBranch (parserAt i) (zeroAt 3) (literal 3 1)) xs = _
  rw [branchEvaluation,parserValue,zeroEvaluation,literalEvaluation]
  cases unpack (xs.get i) <;> rfl

private theorem payloadValue (i : Fin 3) (xs : List.Vector Nat 3) (ys : List Nat)
    (parsed : unpack (xs.get i) = some ys) :
    evaluate (payloadAt i) xs = numbersNumber ys := by
  change evaluate (.composition predOne ![parserAt i]) xs = _
  rw [compositeOne,parserValue,parsed]
  exact predEvaluation (numbersNumber ys + 1)

private theorem numericalCore (s k r : List Nat) :
    evaluate partitionScratch (numbersNumber s ::ᵥ numbersNumber k ::ᵥ numbersNumber r ::ᵥ nil) =
      (decide (s.Perm (k ++ r))).toNat := by
  unfold partitionScratch observePartition appendKeptRemoved
  rw [compositeTwo,compositeTwo]
  change evaluate permutation
    (numbersNumber s ::ᵥ evaluate append (numbersNumber k ::ᵥ numbersNumber r ::ᵥ nil) ::ᵥ nil) = _
  have ha := appendEvaluation (numbersNumber k) r
  rw [numbersRoundTrip,vectorTwo] at ha
  simp only [Option.getD_some] at ha
  rw [ha]
  simpa only [vectorTwo] using numericPermutation s (k ++ r)

theorem exact_NumericSourcePartition : ExactNumericSourcePartition := by
  intro src kept removed
  let xs := src ::ᵥ kept ::ᵥ removed ::ᵥ nil
  change evaluate (conjunction parsedAll partitionCall) xs = _
  have sReady : evaluate (parsedAt 0) xs = (unpack src).isSome.toNat := readyValue 0 xs
  have kReady : evaluate (parsedAt 1) xs = (unpack kept).isSome.toNat := readyValue 1 xs
  have rReady : evaluate (parsedAt 2) xs = (unpack removed).isSome.toNat := readyValue 2 xs
  unfold parsedAll
  rw [bothEvaluation,bothEvaluation,bothEvaluation,sReady,kReady,rReady]
  cases hs : unpack src with
  | none => simp [expected,hs]
  | some s =>
    cases hk : unpack kept with
    | none => simp [expected,hs,hk]
    | some k =>
      cases hr : unpack removed with
      | none => simp [expected,hs,hk,hr]
      | some r =>
        have ran : evaluate partitionCall xs = (decide (s.Perm (k ++ r))).toNat := by
          unfold partitionCall decodedCall
          rw [compositeThree,payloadValue 0 xs s hs,payloadValue 1 xs k hk,payloadValue 2 xs r hr]
          exact numericalCore s k r
        cases h : decide (s.Perm (k ++ r)) <;> simp [expected,hs,hk,hr,ran,h]

#print axioms exact_NumericSourcePartition

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionNumericProof
