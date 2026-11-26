module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunIterationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne)
open NumberedWindowRawContextAlgorithm (RawRoot State tick iterate)
open NumberedWindowInternalSparseRawTick (encodeState chosenTick)
open NumberedWindowInternalSparseRawTickNumericChecks (exact_OriginalEncodedTick)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalSparseRawRunTargets

/-- Original head-first recursion commutes with one actual tick. -/
private theorem tickIterate (r : RawRoot) (fuel : Nat) (s : State) :
    tick r (iterate r fuel s) = iterate r fuel (tick r s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih => exact ih (tick r s)

private theorem stepValue (p other : Program 3) (fuel previous initial : Nat) :
    evaluate (step p other) (fuel ::ᵥ previous ::ᵥ initial ::ᵥ nil) =
      evaluate (chosenTick p other) (previous ::ᵥ nil) := by
  change evaluate (chosenTick p other)
    (List.Vector.ofFn (fun _ : Fin 1 => previous)) = _
  rw [vectorOne]

theorem loop : ExactOriginalRawIteration := by
  intro root p other hp ho fuel
  induction fuel with
  | zero =>
    intro s
    rfl
  | succ k ih =>
    intro s
    change evaluate (step p other) (k ::ᵥ
      evaluate (iterateState p other) (k ::ᵥ encodeState s ::ᵥ nil) ::ᵥ encodeState s ::ᵥ nil) = _
    rw [stepValue,ih s,exact_OriginalEncodedTick root p other hp ho]
    change encodeState (tick root (iterate root k s)) = encodeState (iterate root k (tick root s))
    rw [tickIterate]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunIterationProof
