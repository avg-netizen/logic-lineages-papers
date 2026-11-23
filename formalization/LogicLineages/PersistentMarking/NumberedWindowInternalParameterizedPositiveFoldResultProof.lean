module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldFuelProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalListCodec (headCode tailCode)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
  (vectorFour vectorFive scratchHead scratchTail)

private theorem stateValue (A : Program 4) (c ty start cert : Nat) :
    evaluate (stateAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      evaluate (iterateAt A) (cert ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) := by
  unfold stateAt
  rw [evaluate,vectorFive] <;> rfl

private theorem fromState (q : Program 1) (A : Program 4) (c ty start cert : Nat) :
    evaluate (.composition q (fun _ : Fin 1 => stateAt A)) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      run q (evaluate (stateAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil)) := by
  rw [evaluate,vectorOne] <;> rfl

theorem exact_ParameterizedFinishValue (A : Program 4) (c ty start cert : Nat) :
    evaluate (finishAt A) (c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      encodeState (foldPhysical A c ty start cert) := by
  unfold finishAt
  rw [evalBranch,fromState,stateValue,exact_ParameterizedFuelDecoded A c ty start cert cert (Nat.le_refl _),
    scratchHead,if_pos rfl]
  rw [fromState,stateValue,exact_ParameterizedFuelDecoded A c ty start cert cert (Nat.le_refl _),scratchTail]

private theorem walkValue (A : Program 4) (c ty source cert target : Nat) :
    evaluate (walkAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      encodeState (foldPhysical A c ty (source+1) cert) := by
  unfold walkAt
  rw [evaluate,vectorFour]
  change evaluate (finishAt A) (c ::ᵥ ty ::ᵥ (source+1) ::ᵥ cert ::ᵥ nil) = _
  exact exact_ParameterizedFinishValue A c ty (source+1) cert

private theorem successCode (x : Option Nat) (target : Nat) :
    encodeState x = target+1 ↔ x = some target := by
  cases x <;> simp [encodeState]

/-- Numeric calibration of the literal original positive checker parameterized
only by its physical per-cell advance. Empty source certificate is rejected
even if its decoded fold would retain the initial state. -/
theorem exact_ParameterizedPositiveValue (A : Program 4) (c ty source cert target : Nat) :
    evaluate (positiveAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) =
      if cert ≠ 0 ∧ foldPhysical A c ty (source+1) cert = some target then 1 else 0 := by
  unfold positiveAt
  rw [conjunctionEvaluation,evalBranch]
  let args := c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil
  change (if (if cert = 0 then 0 else 1) = 1 ∧
    evaluate (.composition InternalEqualityTest.equalityTest
      ![walkAt A,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))]) args = 1
    then 1 else 0) = _
  by_cases empty : cert = 0
  · simp [empty]
  · have compared : evaluate (.composition InternalEqualityTest.equalityTest
        ![walkAt A,.composition .succ (fun _ : Fin 1 => .projection (4 : Fin 5))]) args =
        if encodeState (foldPhysical A c ty (source+1) cert) = target+1 then 1 else 0 := by
      dsimp only [args]
      rw [evaluate,vectorTwo]
      change evaluate InternalEqualityTest.equalityTest
        (evaluate (walkAt A) (c ::ᵥ ty ::ᵥ source ::ᵥ cert ::ᵥ target ::ᵥ nil) ::ᵥ
          (target+1) ::ᵥ nil) = _
      rw [walkValue,exactEqualityEvaluation]
    by_cases accepts : foldPhysical A c ty (source+1) cert = some target
    · simp [compared,empty,accepts,encodeState]
    · have different : encodeState (foldPhysical A c ty (source+1) cert) ≠ target+1 :=
        fun h => accepts ((successCode _ _).mp h)
      simp [compared,empty,accepts,different]

#print axioms exact_ParameterizedFinishValue
#print axioms exact_ParameterizedPositiveValue

end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
