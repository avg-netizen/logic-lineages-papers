module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeNumericThinChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne exactPredecessorEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparseFieldCell NumberedWindowInternalSparseFieldCellTargets
open NumberedWindowInternalSparseDecode (good chosenDecode)
open NumberedWindowInternalSparseDecodeNumericThinChecks (exact_AllInputDecoder)

private theorem predecessorValue (p : Program 1) (n : Nat) :
    evaluate (atPredecessor p) ((n+1) ::ᵥ nil) = evaluate p (n ::ᵥ nil) := by
  unfold atPredecessor
  rw [evaluate,vectorOne]
  change evaluate p (evaluate InternalEqualityTest.predecessor ((n+1) ::ᵥ nil) ::ᵥ nil) = _
  rw [exactPredecessorEvaluation] <;> rfl

private theorem nilValue : evaluate cellGood (0 ::ᵥ nil) = 0 := by
  unfold cellGood
  rw [evalBranch] <;> rfl

private theorem succValue (n : Nat) :
    evaluate cellGood ((n+1) ::ᵥ nil) = evaluate good (n ::ᵥ nil) := by
  unfold cellGood
  rw [evalBranch]
  change (if n+1 = 0 then 0 else evaluate (atPredecessor good) ((n+1) ::ᵥ nil)) = _
  rw [if_neg (Nat.succ_ne_zero n),predecessorValue]

theorem allInput : AllInputCell := by
  constructor
  · simp [chosenCell,nilValue]
  · intro n
    have selected : chosenCell (n+1) = chosenDecode n := by
      simp only [chosenCell,chosenDecode,cellHead,cellTail,succValue,predecessorValue]
    exact selected.trans (exact_AllInputDecoder n)

theorem fieldStep : ActualFieldStep := by
  intro state
  rcases state with _ | ⟨n,acc⟩
  · rfl
  cases n with
  | zero => rfl
  | succ n =>
    simp only [chosenStep,NumberedWindowFieldAlgorithm.step,allInput.2 n] <;>
      cases NumberedWindowPairAlgorithm.decode n <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
