module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldResultEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalListCodec (headCode tailCode)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof

private theorem chosenValue (raw : Program 5) (p : Program 3) (c ty start cert : Nat) :
    evaluate (chosenState raw p) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      evaluate (iterateState raw p) (cert ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) := by
  unfold chosenState
  rw [evaluate,vectorFive] <;> rfl

private theorem fromChosen (q : Program 1) (raw : Program 5) (p : Program 3) (c ty start cert : Nat) :
    evaluate (.composition q (fun _ : Fin 1 => chosenState raw p)) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      run q (evaluate (chosenState raw p) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil)) := by
  rw [evaluate,vectorOne] <;> rfl

theorem finishValue (entries : Entries) (s : Settings) (raw : Program 5) (p : Program 3)
    (done : ActualFuelCalibration entries s raw p) (c ty start cert : Nat) :
    evaluate (finish raw p) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      encodeState (originalFold entries s c ty start cert) := by
  unfold finish
  rw [evalBranch,fromChosen,chosenValue,done c ty start cert cert (Nat.le_refl _),scratchHead,if_pos rfl]
  rw [fromChosen,chosenValue,done c ty start cert cert (Nat.le_refl _),scratchTail]

private theorem walkValue (entries : Entries) (s : Settings) (raw : Program 5) (p : Program 3)
    (done : ActualFuelCalibration entries s raw p) (c ty source cert target : Nat) :
    evaluate (chosenWalk raw p) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      encodeState (originalFold entries s c ty (source+1) cert) := by
  unfold chosenWalk
  rw [evaluate,vectorFour]
  change evaluate (finish raw p) (c ::ᵥ ty ::ᵥ (source+1) ::ᵥ cert ::ᵥ nil) = _
  exact finishValue entries s raw p done c ty (source+1) cert

private theorem successCode (x : Option Nat) (target : Nat) :
    encodeState x = target+1 ↔ x = some target := by
  cases x <;> simp [encodeState]

theorem checkValue (entries : Entries) (s : Settings) (raw : Program 5) (p : Program 3)
    (done : ActualFuelCalibration entries s raw p) (c ty source cert target : Nat) :
    evaluate (positive raw p) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      if cert ≠ 0 ∧ originalFold entries s c ty (source+1) cert = some target then 1 else 0 := by
  unfold positive
  rw [conjunctionEvaluation,evalBranch]
  let args := c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil
  change (if (if cert = 0 then 0 else 1) = 1 ∧
    evaluate (.composition InternalEqualityTest.equalityTest
      ![chosenWalk raw p,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))]) args = 1
    then 1 else 0) = _
  by_cases empty : cert = 0
  · simp [empty]
  · have compared : evaluate (.composition InternalEqualityTest.equalityTest
        ![chosenWalk raw p,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))]) args =
        if encodeState (originalFold entries s c ty (source+1) cert) = target+1 then 1 else 0 := by
      dsimp only [args]
      rw [evaluate,vectorTwo]
      change evaluate InternalEqualityTest.equalityTest
        (evaluate (chosenWalk raw p) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) ::ᵥ
          (target+1) ::ᵥ nil) = _
      rw [walkValue entries s raw p done,exactEqualityEvaluation]
    by_cases accepts : originalFold entries s c ty (source+1) cert = some target
    · simp [compared,empty,accepts,encodeState]
    · have different : encodeState (originalFold entries s c ty (source+1) cert) ≠ target+1 :=
        fun h => accepts ((successCode _ _).mp h)
      simp [compared,empty,accepts,different]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldResultEvaluationProof
