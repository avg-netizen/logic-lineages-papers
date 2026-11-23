module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericPartitionsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open NumberedWindowInternalFreshProbeDispatchProgram (chooseBranch zeroAt predOne literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo compositeThree branchEvaluation zeroEvaluation literalEvaluation predEvaluation vectorTwo)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck allReady mapAt mapReady mapPayload)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets mapped)
open NumberedWindowInternalDirectInsertedTargetsMap (exactRawInsertedTargets)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalDirectCoreNumericTargets
open NumberedWindowInternalDirectCoreNumericSupportProof

private theorem observeValue (count : Program 2) (fit : CountFit count) (s k a : List Nat) :
    evaluate (observePartition count) (numbersNumber s ::ᵥ numbersNumber k ::ᵥ numbersNumber a ::ᵥ nil) =
      (decide (s.Perm (k ++ a))).toNat := by
  change evaluate (.composition count (Fin.cons (.projection 0) (Fin.cons appendKeptRemoved Fin.elim0))) _ = _
  rw [compositeTwo]
  have appended : evaluate appendKeptRemoved (numbersNumber s ::ᵥ numbersNumber k ::ᵥ numbersNumber a ::ᵥ nil) =
      numbersNumber (k ++ a) := by
    change evaluate (.composition append (Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0))) _ = _
    rw [compositeTwo]
    exact appendValue k a
  rw [appended]
  exact fit s (k ++ a)

theorem exact_NumericSourceObserver (count : Program 2) (fit : CountFit count) (src kept removed : Nat) :
    evaluate (rawSourceCheck (observePartition count)) (src ::ᵥ kept ::ᵥ removed ::ᵥ nil) =
      (partition (unpack src) (unpack kept) (unpack removed)).toNat := by
  let xs := src ::ᵥ kept ::ᵥ removed ::ᵥ nil
  let p := observePartition count
  change evaluate (conjunction parsedAll (decodedCall p)) xs = _
  have hs0 : evaluate (parsedAt 0) xs = (unpack src).isSome.toNat := readyValue 0 xs
  have hk0 : evaluate (parsedAt 1) xs = (unpack kept).isSome.toNat := readyValue 1 xs
  have ha0 : evaluate (parsedAt 2) xs = (unpack removed).isSome.toNat := readyValue 2 xs
  simp only [parsedAll,conjunctionBit,hs0,hk0,ha0,decideToNatOne]
  cases hs : unpack src with
  | none => simp [partition,hs]
  | some s =>
    cases hk : unpack kept with
    | none => simp [partition,hs,hk]
    | some k =>
      cases ha : unpack removed with
      | none => simp [partition,hs,hk,ha]
      | some a =>
        have ran : evaluate (decodedCall p) xs = (decide (s.Perm (k ++ a))).toNat := by
          change evaluate (.composition p (Fin.cons (payloadAt 0)
            (Fin.cons (payloadAt 1) (Fin.cons (payloadAt 2) Fin.elim0)))) xs = _
          rw [compositeThree,payloadValue 0 xs s hs,payloadValue 1 xs k hk,payloadValue 2 xs a ha]
          exact observeValue count fit s k a
        simp [partition,hs,hk,ha,ran,decideToNatOne]

private theorem mapValue (dst kept inserted : Nat) :
    evaluate mapAt (dst ::ᵥ kept ::ᵥ inserted ::ᵥ nil) =
      encodeResult ((actualEntries inserted).map (List.map Prod.fst)) := by
  change evaluate (.composition insertedTargets (Fin.cons (.projection 2) Fin.elim0)) _ = _
  rw [compositeOne]
  change evaluate insertedTargets (inserted ::ᵥ nil) = _
  have h := exactRawInsertedTargets inserted
  unfold actualEntries
  cases hu : unpack inserted <;> simpa only [hu,Option.bind,Option.map,mapped] using h

private theorem mapReadyValue (dst kept inserted : Nat) :
    evaluate mapReady (dst ::ᵥ kept ::ᵥ inserted ::ᵥ nil) = (actualEntries inserted).isSome.toNat := by
  change evaluate (chooseBranch mapAt (zeroAt 3) (literal 3 1)) _ = _
  rw [branchEvaluation,mapValue,zeroEvaluation,literalEvaluation]
  cases actualEntries inserted <;> rfl

private theorem mapPayloadValue (dst kept inserted : Nat) (a : List NumberedWindowDirectAlgorithm.Entry)
    (h : actualEntries inserted = some a) :
    evaluate mapPayload (dst ::ᵥ kept ::ᵥ inserted ::ᵥ nil) = numbersNumber (a.map Prod.fst) := by
  change evaluate (.composition predOne (Fin.cons mapAt Fin.elim0)) _ = _
  rw [compositeOne,mapValue,h]
  exact predEvaluation (numbersNumber (a.map Prod.fst) + 1)

theorem exact_NumericTargetObserver (count : Program 2) (fit : CountFit count) (dst kept inserted : Nat) :
    evaluate (rawTargetCheck count) (dst ::ᵥ kept ::ᵥ inserted ::ᵥ nil) =
      (partition (unpack dst) (unpack kept) ((actualEntries inserted).map (List.map Prod.fst))).toNat := by
  let xs := dst ::ᵥ kept ::ᵥ inserted ::ᵥ nil
  let c := NumberedWindowInternalDirectTargetPartitionRawTargets.decodeCall count
  change evaluate (conjunction allReady c) xs = _
  have hd0 : evaluate (parsedAt 0) xs = (unpack dst).isSome.toNat := readyValue 0 xs
  have hk0 : evaluate (parsedAt 1) xs = (unpack kept).isSome.toNat := readyValue 1 xs
  have hm0 : evaluate mapReady xs = (actualEntries inserted).isSome.toNat := mapReadyValue dst kept inserted
  simp only [allReady,conjunctionBit,hd0,hk0,hm0,decideToNatOne]
  cases hd : unpack dst with
  | none => simp [partition,hd]
  | some d =>
    cases hk : unpack kept with
    | none => simp [partition,hd,hk]
    | some k =>
      cases ha : actualEntries inserted with
      | none => simp [partition,hd,hk,ha]
      | some a =>
        have ran : evaluate c xs = (decide (d.Perm (k ++ a.map Prod.fst))).toNat := by
          change evaluate (.composition (observePartition count) (Fin.cons (payloadAt 0)
            (Fin.cons (payloadAt 1) (Fin.cons mapPayload Fin.elim0)))) xs = _
          rw [compositeThree,payloadValue 0 xs d hd,payloadValue 1 xs k hk,mapPayloadValue dst kept inserted a ha]
          exact observeValue count fit d k (a.map Prod.fst)
        simp [partition,hd,hk,ha,ran,decideToNatOne]

#print axioms exact_NumericSourceObserver
#print axioms exact_NumericTargetObserver
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericPartitionsProof
