module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositive
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldResultProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSlotsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseAddressPositive (atAddress sideGood sameField addressPositive)
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof (tape sourceEval targetEval acceptedBoth)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof (vectorFive)
open NumberedWindowInternalSparsePositiveFoldTargets (ActualPositiveCalibration packedPositive)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualAdvanceCalibration)
open NumberedWindowInternalZeroRankPositiveFoldResultProof (exact_OriginalZeroRankPositiveAccepts)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedAddressPositive

attribute [local irreducible] positive zeroPositive sideGood sameField

theorem exact_ParameterizedAddressCall (P : Program 5) (x w y : Nat) :
    evaluate (wrapFoldAt P) (tape x w y) =
      evaluate P
        (run rawContext x ::ᵥ run rawResult x ::ᵥ run rawLeast x ::ᵥ w ::ᵥ run rawLeast y ::ᵥ nil) := by
  let Q : Fin 5 → Program 3 :=
    ![atAddress rawContext 0,atAddress rawResult 0,atAddress rawLeast 0,.projection 1,atAddress rawLeast 2]
  change evaluate P (List.Vector.ofFn fun i : Fin 5 => evaluate (Q i) (tape x w y)) = _
  rw [vectorFive]
  change evaluate P (evaluate (atAddress rawContext 0) (tape x w y) ::ᵥ
    evaluate (atAddress rawResult 0) (tape x w y) ::ᵥ evaluate (atAddress rawLeast 0) (tape x w y)
      ::ᵥ w ::ᵥ evaluate (atAddress rawLeast 2) (tape x w y) ::ᵥ nil) = _
  simp only [sourceEval,targetEval]

theorem exact_OriginalZeroRankAddressAccepts (entries : Entries) (s : Settings)
    (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (stepFit : ActualAdvanceCalibration entries s raw L)
    (posFit : ActualPositiveCalibration entries s raw L)
    (gFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d)
    (x w y : Nat) :
    evaluate (zeroAddress cv tv g raw L) (tape x w y) = 1 ↔
      evaluate (addressPositive cv tv raw L) (tape x w y) = 1 ∧ rawRank (run rawLeast y) = 0 := by
  rw [← exact_OriginalAddressAt cv tv raw L]
  simp only [zeroAddress,addressAt,acceptedBoth,exact_ParameterizedAddressCall,
    exact_OriginalZeroRankPositiveAccepts entries s g raw L stepFit gFit]
  rw [posFit (run rawContext x) (run rawResult x) (run rawLeast x) w (run rawLeast y)]
  have bit : (if packedPositive entries s (run rawContext x) (run rawResult x) (run rawLeast x) w
      (run rawLeast y) = true then (1 : Nat) else 0) = 1 ↔
      packedPositive entries s (run rawContext x) (run rawResult x) (run rawLeast x) w
        (run rawLeast y) = true := by
    cases packedPositive entries s (run rawContext x) (run rawResult x) (run rawLeast x) w
      (run rawLeast y) <;> decide
  rw [bit]
  simp only [and_assoc]

#print axioms exact_ParameterizedAddressCall
#print axioms exact_OriginalZeroRankAddressAccepts

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAddressNumericProof
