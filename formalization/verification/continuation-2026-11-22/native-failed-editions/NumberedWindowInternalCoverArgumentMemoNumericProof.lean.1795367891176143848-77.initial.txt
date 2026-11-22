module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (bounds argsNext table)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowRawExchangeVerticesBoundsTableProof (previous)
open NumberedWindowRawExchangeVerticesCodecProof (decoded)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure combine readMeasure auxiliaryMeasure)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalChosenAuxMeasureCombineNumericProof (exact_ChosenAuxMeasureCombine)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail atPredecessor)
open NumberedWindowInternalSparseDecode (good gap)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (flagOfCell headTailOfCell noFlagOfNone)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverArgumentMemoTargets

private theorem source (n : Nat) :
    (bounds (n+1)).2 = ((decode n).map (fun p =>
      let q := ((table (n+1)).getD p.1 default).1
      let r := ((table (n+1)).getD p.2 default).2
      (q.1+1+r.1,max q.2 r.2))).getD default := rfl

private theorem goodCode (n head tail : Nat) (read : decode n = some (head,tail)) :
    Encodable.encode (bounds (n+1)).2 =
      combine (Encodable.encode (bounds head).1) (Encodable.encode (bounds tail).2) := by
  obtain ⟨_, h, t⟩ := decoded read
  have equal : (bounds (n+1)).2 = auxiliaryMeasure (bounds head).1 (bounds tail).2 := by
    rw [source,read]
    change (((table (n+1)).getD head default).1.1 + 1 + ((table (n+1)).getD tail default).2.1,
      max ((table (n+1)).getD head default).1.2 ((table (n+1)).getD tail default).2.2) = _
    rw [previous (Nat.lt_succ_of_le h),previous (Nat.lt_succ_of_le t)]
    unfold auxiliaryMeasure
    congr 1
    omega
  simp only [combine,readMeasure,Encodable.encodek,Option.getD_some,equal]

private theorem currentValue (n old : Nat) : evaluate currentKey (args n old) = n+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem argumentCellValue (n old : Nat) :
    evaluate argumentCell (args n old) = run cellGood (n+1) := by
  rw [argumentCell,unaryValue,currentValue] <;> rfl

private theorem step (F : Program 1) (fits : TermMeasureCalibrated F) (n old : Nat)
    (earlier : ∀ k, k < n+1 → evaluate lookup ((n-k) ::ᵥ old ::ᵥ nil) = Encodable.encode (bounds k).2) :
    evaluate (argumentUpdate F) (args n old) = Encodable.encode (bounds (n+1)).2 := by
  rw [argumentUpdate,evalBranch,argumentCellValue]
  cases read : decode n with
  | none =>
    have absent := (allInput.2 n).trans read
    have fail : run cellGood (n+1) = 0 := by
      have non := noFlagOfNone absent
      have bits : run cellGood (n+1) = 0 ∨ run cellGood (n+1) = 1 := by
        have pos : n+1 ≠ 0 := Nat.succ_ne_zero n
        unfold run cellGood
        rw [evalBranch]
        change (if n+1 = 0 then 0 else evaluate (atPredecessor good) ((n+1) ::ᵥ nil)) = 0 ∨
          (if n+1 = 0 then 0 else evaluate (atPredecessor good) ((n+1) ::ᵥ nil)) = 1
        rw [if_neg pos]
        change evaluate good (List.Vector.ofFn (fun _ : Fin 1 =>
            evaluate InternalEqualityTest.predecessor ((n+1) ::ᵥ nil))) = 0 ∨ _
        rw [good,evalBranch]
        split
        · right; rfl
        · left; rfl
      exact bits.resolve_right non
    rw [fail,if_pos rfl,source,read]
    rfl
  | some pair =>
    rcases pair with ⟨head,tail⟩
    have found := (allInput.2 n).trans read
    have ⟨h,t⟩ := headTailOfCell found
    have tailSmall := Nat.lt_succ_of_le (decoded read).2.2
    have headValue : evaluate (headMeasure F) (args n old) = Encodable.encode (bounds head).1 := by
      rw [headMeasure,unaryValue,argumentHead,unaryValue,currentValue]
      change evaluate F (run cellHead (n+1) ::ᵥ nil) = _
      rw [h]
      exact fits head
    have tailValue : evaluate tailMeasure (args n old) = Encodable.encode (bounds tail).2 := by
      rw [tailMeasure,binaryValue,tailOffset,binaryValue,argumentTail,unaryValue,currentValue]
      change evaluate lookup
        (evaluate InternalEqualityTest.subtract (run cellTail (n+1) ::ᵥ n ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
      rw [t,exactSubtractionEvaluation]
      exact earlier tail tailSmall
    rw [flagOfCell found,if_neg (by decide),binaryValue,headValue,tailValue,exact_ChosenAuxMeasureCombine]
    exact (goodCode n head tail read).symm

private theorem row (F : Program 1) (fits : TermMeasureCalibrated F) (n : Nat) :
    evaluate (scratchRow (constantZero 2) (argumentUpdate F)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      Encodable.encode (bounds n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ n =>
      rw [rowSucc]
      apply step F fits
      intro child small
      rw [lookupAt (constantZero 2) (argumentUpdate F) (0 ::ᵥ 0 ::ᵥ nil) n child
        (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverArgumentMemo : ExactCoverArgumentMemo := by
  intro F fits n
  unfold argumentMeasure
  rw [selectedMeasure,compositeThree]
  exact row F fits n

#print axioms exact_CoverArgumentMemo

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoNumericProof
