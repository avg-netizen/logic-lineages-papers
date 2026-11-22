module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowCoverBoundsAlgorithm (bounds termMeasure table)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowRawExchangeVerticesBoundsTableProof (termBounds previous)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverNamedLeafMeasureNumericProof (exact_CoverNamedLeafSharedMeasure)
open NumberedWindowInternalCoverLambdaMeasureRowNumericProof (exact_CoverLambdaBumpCalibration)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaBump)
open NumberedWindowInternalCoverOrdinaryMeasureTargets

private theorem fieldValue {raw h a : Nat} (read : unpackNode raw = some (4,[h,a])) :
    run (field 1) raw = a := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 4 (pack [h,a]))).2
  have middle : run cellTail (pack [h,a]) = pack [a] := (headTailOfCell (cellAt h (pack [a]))).2
  have inner : run cellHead (pack [a]) = a := (headTailOfCell (cellAt a (pack []))).1
  change run (field 1) (NumberedWindowPairAlgorithm.pair 4 (pack [h,a]) + 1) = a
  simp only [field,cursor,applyValue,outer,middle,inner]

private theorem actualBounds {raw h a : Nat} (read : unpackNode raw = some (4,[h,a])) :
    (bounds raw).1 = ((bounds a).2.1+1,(bounds a).2.2) := by
  have small := (nodeBounds read).2 a (by simp)
  rw [termBounds read]
  change (((table raw).getD a default).2.1+1,((table raw).getD a default).2.2) = _
  rw [previous small]

theorem exact_CoverSelectedArgsMeasure : ExactCoverSelectedArgsMeasure := by
  intro A calibrated a
  change evaluate (selectedArgsMeasure A) (a ::ᵥ nil) = Encodable.encode (bounds a).2
  rw [selectedArgsMeasure,evalBranch]
  change (if a = 0 then 0 else evaluate A (a ::ᵥ nil)) = _
  cases a with
  | zero => rfl
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    exact calibrated (n+1)

theorem exact_CoverOrdinaryMeasureBase : ExactCoverOrdinaryMeasureBase := by
  intro M A calibrated args raw
  change evaluate (ordinaryMeasureBase M A) (raw ::ᵥ nil) = Encodable.encode (bounds raw).1
  rw [ordinaryMeasureBase,evalBranch]
  by_cases yes : run (header 4 2) raw = 1
  · obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode 4 2 raw).mp yes
    rcases fs with _ | ⟨h,_ | ⟨a,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    change evaluate (header 4 2) (raw ::ᵥ nil) = 1 at yes
    rw [yes,if_neg (by decide)]
    change run lambdaBump (evaluate (selectedArgsMeasure A) (run (field 1) raw ::ᵥ nil)) = _
    rw [fieldValue read,exact_CoverSelectedArgsMeasure A args a,actualBounds read]
    exact exact_CoverLambdaBumpCalibration (bounds a).2.1 (bounds a).2.2
  · have zero : run (header 4 2) raw = 0 := by
      have bits : run (header 4 2) raw = 0 ∨ run (header 4 2) raw = 1 := by
        unfold run header nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bits.resolve_right yes
    rw [if_pos zero]
    exact calibrated raw

theorem exact_CoverOrdinarySharedMeasure : ExactCoverOrdinarySharedMeasure := by
  intro M A calibrated args
  exact exact_CoverNamedLeafSharedMeasure (ordinaryMeasureBase M A)
    (exact_CoverOrdinaryMeasureBase M A calibrated args)

#print axioms exact_CoverSelectedArgsMeasure
#print axioms exact_CoverOrdinaryMeasureBase
#print axioms exact_CoverOrdinarySharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNumericProof
