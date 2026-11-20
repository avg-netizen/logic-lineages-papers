module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunInitialProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunOwnProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowRawContextAlgorithm (RawRoot State iterate run)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparseRawFunctionFrame (encodeFrame)
open NumberedWindowInternalSparseRawTick (encodeState)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawRun
open NumberedWindowInternalSparseRawRunTargets
open NumberedWindowInternalSparseRawRunInitialProof (initial)
open NumberedWindowInternalSparseRawRunIterationProof (loop)

private theorem flag (s : State) :
    evaluate cellHead (encodeState s ::ᵥ nil) = s.1.toNat :=
  (headTailOfCell (cellAt s.1.toNat (pack [encodeFrame s.2]))).1

private theorem runState (root : RawRoot) (p other : Program 3)
    (hp : ActualRoot root p) (ho : ActualFallback other) (q w r : Nat) :
    evaluate (ownState p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) =
      encodeState (iterate root w (false,some (q,w,r))) := by
  let v := q ::ᵥ w ::ᵥ r ::ᵥ nil
  change evaluate (iterateState p other) (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![.projection 1,initialState] : Fin 2 → Program 3) i) v)) = _
  rw [vectorTwo]
  change evaluate (iterateState p other) (w ::ᵥ evaluate initialState v ::ᵥ nil) = _
  rw [initial q w r]
  exact loop root p other hp ho w (false,some (q,w,r))

theorem own : ExactOriginalOwnRawRun := by
  intro root p other hp ho q w r
  let v := q ::ᵥ w ::ᵥ r ::ᵥ nil
  change evaluate cellHead (List.Vector.ofFn (fun _ : Fin 1 => evaluate (ownState p other) v)) = _
  rw [vectorOne]
  change evaluate cellHead (evaluate (ownState p other) v ::ᵥ nil) = _
  rw [runState root p other hp ho q w r,flag] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunOwnProof
