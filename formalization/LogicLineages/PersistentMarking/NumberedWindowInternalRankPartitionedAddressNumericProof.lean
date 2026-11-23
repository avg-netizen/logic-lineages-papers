module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddress
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof (tape targetEval)
open NumberedWindowInternalSparsePositiveFoldTargets (ActualPositiveCalibration)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualAdvanceCalibration)
open NumberedWindowInternalZeroRankAddressNumericProof (exact_OriginalZeroRankAddressAccepts)
open NumberedWindowInternalParameterizedAddressPositive (zeroAddress addressAt)
open NumberedWindowInternalRankPartitionedAddress

attribute [local irreducible] NumberedWindowInternalParameterizedPositiveFold.zeroPositive

private theorem picked (g : Program 1) (gFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d)
    (x w y : Nat) : evaluate (targetRank g) (tape x w y) = rawRank (run rawLeast y) := by
  rw [targetRank,targetEval,applyValue]
  exact gFit _

private theorem isOldBit (cv tv : Program 1) (raw : Program 5) (L : Program 3) (x w y : Nat) :
    evaluate (addressPositive cv tv raw L) (tape x w y) = 0 ∨
    evaluate (addressPositive cv tv raw L) (tape x w y) = 1 := by
  unfold addressPositive
  rw [conjunctionEvaluation]
  split <;> simp

private theorem isNewBit (cv tv g : Program 1) (raw : Program 5) (L : Program 3) (x w y : Nat) :
    evaluate (zeroAddress cv tv g raw L) (tape x w y) = 0 ∨
    evaluate (zeroAddress cv tv g raw L) (tape x w y) = 1 := by
  unfold zeroAddress addressAt
  rw [conjunctionEvaluation]
  split <;> simp

theorem exact_OriginalRankPartitionedAddressNumeric (entries : Entries) (s : Settings)
    (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (stepFit : ActualAdvanceCalibration entries s raw L)
    (posFit : ActualPositiveCalibration entries s raw L)
    (gFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d)
    (x w y : Nat) :
    evaluate (rankPartitionedAddress cv tv g raw L) (tape x w y) =
      evaluate (addressPositive cv tv raw L) (tape x w y) := by
  rw [rankPartitionedAddress,evalBranch,picked g gFit x w y]
  by_cases h : rawRank (run rawLeast y) = 0
  · rw [if_pos h]
    have fit := exact_OriginalZeroRankAddressAccepts entries s cv tv g raw L stepFit posFit gFit x w y
    have same :
        evaluate (zeroAddress cv tv g raw L) (tape x w y) = 1 ↔
          evaluate (addressPositive cv tv raw L) (tape x w y) = 1 := by simpa only [h,and_true] using fit
    rcases isOldBit cv tv raw L x w y with old | old
    · rw [old]
      rcases isNewBit cv tv g raw L x w y with new | new
      · exact new
      · have impossible : (0 : Nat) = 1 := old.symm.trans (same.mp new)
        omega
    · exact (same.mpr old).trans old.symm
  · exact if_neg h

#print axioms exact_OriginalRankPartitionedAddressNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressNumericProof
