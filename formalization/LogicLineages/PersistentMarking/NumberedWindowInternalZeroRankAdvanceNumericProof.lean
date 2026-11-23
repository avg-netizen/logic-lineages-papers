module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
  (exactPredecessorEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)
open NumberedWindowInternalZeroRankAdvance
open NumberedWindowInternalSparsePathAdvanceTargets
  (ActualAdvanceCalibration packedOriginalAdvance encodeState)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

private theorem evalUnary {n : Nat} (g : Program 1) (A : Program n) (xs : List.Vector Nat n) :
    evaluate (unaryAfter g A) xs = evaluate g (evaluate A xs ::ᵥ nil) := by
  unfold unaryAfter
  change evaluate g (List.Vector.ofFn (fun _ : Fin 1 => evaluate A xs)) = _
  rw [vectorOne]

theorem exact_ZeroRankOutputEvaluation {n : Nat} (g : Program 1) (A : Program n) (xs : List.Vector Nat n) :
    evaluate (zeroOutput g A) xs =
      if evaluate g ((evaluate A xs).pred ::ᵥ nil) = 0 then evaluate A xs else 0 := by
  rw [zeroOutput,evalBranch,resultRank,evalUnary,evalUnary,exactPredecessorEvaluation]
  rfl

/-- At each genuine original selected transition, filter exactly the
real output rank; the original witness and all input fields are unchanged. -/
theorem exact_OriginalZeroRankAdvanceNumeric (xs : Entries) (s : Settings)
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (actual : ActualAdvanceCalibration xs s raw L)
    (gFit : ∀ q, evaluate g (q ::ᵥ nil) = rawRank q)
    (ctx ty current hop : Nat) :
    evaluate (zeroOutput g (advance raw L)) (ctx ::ᵥ ty ::ᵥ current ::ᵥ hop ::ᵥ nil) =
      encodeState ((packedOriginalAdvance xs s ctx ty current hop).filter (fun q => rawRank q == 0)) := by
  rw [exact_ZeroRankOutputEvaluation,actual,gFit]
  cases h : packedOriginalAdvance xs s ctx ty current hop with
  | none => simp [encodeState]
  | some y =>
    simp only [encodeState,Nat.pred_succ]
    by_cases z : rawRank y = 0 <;> simp [Option.filter,z,encodeState]

#print axioms exact_ZeroRankOutputEvaluation
#print axioms exact_OriginalZeroRankAdvanceNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceNumericProof
