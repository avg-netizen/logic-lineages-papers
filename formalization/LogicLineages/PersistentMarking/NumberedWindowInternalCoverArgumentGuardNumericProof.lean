module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize evalZeroTest actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowRawExchangeVerticesCodecProof (decoded)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (flagOfCell headTailOfCell noFlagOfNone emptyUnpack missingUnpack splitUnpack)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree literalEvaluation)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentCell argumentHead argumentTail tailMeasure tailOffset)
open NumberedWindowInternalCoverArgumentGuardTargets

private theorem keyValue (n old : Nat) : evaluate currentKey (args n old) = n+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem acceptDecomp (G : Program 1) (n h a : Nat) (read : decode n = some (h,a)) :
    acceptedHeads G (n+1) = ((run G h == 1) && acceptedHeads G a) := by
  have c := (allInput.2 n).trans read
  unfold acceptedHeads run
  rw [splitUnpack c]
  cases e : NumberedWindowFieldAlgorithm.unpack a <;> simp [List.all]

private theorem step (G : Program 1) (n old : Nat)
    (earlier : ∀ k, k < n+1 →
       evaluate lookup ((n-k) ::ᵥ old ::ᵥ nil) = if acceptedHeads G k then 0 else 1) :
    evaluate (argumentRejectUpdate G) (args n old) = if acceptedHeads G (n+1) then 0 else 1 := by
  rw [argumentRejectUpdate,evalBranch,evalNormalize,literalEvaluation]
  have zz : evaluate (constantZero 4) (args n old) = 0 := rfl
  rw [zz]
  cases read : decode n with
  | none =>
    have absent := (allInput.2 n).trans read
    have off := noFlagOfNone absent
    have bad : evaluate (argumentGuard G) (args n old) = 0 := by
      rw [argumentGuard,actualConjunctionEvaluation,argumentCell,unaryValue,keyValue]
      simp only [off,false_and,if_false]
    have failed : acceptedHeads G (n+1) = false := by
      rw [acceptedHeads,missingUnpack (Nat.succ_ne_zero n) absent]
      rfl
    rw [bad,failed] <;> rfl
  | some pair =>
    rcases pair with ⟨h,a⟩
    have found := (allInput.2 n).trans read
    obtain ⟨hh,aa⟩ := headTailOfCell found
    have bound := Nat.lt_succ_of_le (decoded read).2.2
    have hOut : evaluate (argumentHeadAccept G) (args n old) = run G h := by
      rw [argumentHeadAccept,unaryValue,argumentHead,unaryValue,keyValue,hh]
    have aOut : evaluate tailMeasure (args n old) = if acceptedHeads G a then 0 else 1 := by
      rw [tailMeasure,binaryValue,tailOffset,binaryValue,argumentTail,unaryValue,keyValue,aa]
      change evaluate lookup (evaluate InternalEqualityTest.subtract (a ::ᵥ n ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
      rw [exactSubtractionEvaluation]
      exact earlier a bound
    have tOut : evaluate argumentTailAccept (args n old) = if acceptedHeads G a then 1 else 0 := by
      rw [argumentTailAccept,unaryValue,aOut]
      cases eq : acceptedHeads G a <;> rfl
    have gate : evaluate (argumentGuard G) (args n old) =
        if run G h = 1 ∧ acceptedHeads G a = true then 1 else 0 := by
      rw [argumentGuard,actualConjunctionEvaluation,actualConjunctionEvaluation,
        argumentCell,unaryValue,keyValue,flagOfCell found,hOut,tOut]
      by_cases head : run G h = 1 <;> cases tail : acceptedHeads G a <;> simp [head,tail]
    have source := acceptDecomp G n h a read
    by_cases head : run G h = 1 <;> cases tail : acceptedHeads G a <;>
      simp [gate,source,head,tail]

private theorem row (G : Program 1) (n : Nat) :
    evaluate (scratchRow (constantZero 2) (argumentRejectUpdate G)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      if acceptedHeads G n then 0 else 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero,acceptedHeads,emptyUnpack] <;> rfl
    | succ n =>
      rw [rowSucc]
      apply step G
      intro child small
      rw [lookupAt (constantZero 2) (argumentRejectUpdate G) (0 ::ᵥ 0 ::ᵥ nil) n child
        (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverArgumentGuardNumeric : ExactCoverArgumentGuardNumeric := by
  intro G n
  unfold argumentReject
  rw [selectedMeasure,compositeThree]
  exact row G n

#print axioms exact_CoverArgumentGuardNumeric

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardNumericProof
