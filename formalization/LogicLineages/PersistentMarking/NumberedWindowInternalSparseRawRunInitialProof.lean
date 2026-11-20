module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunInitialProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalEqualityTestEvaluationProof (vectorOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo)
open NumberedWindowInternalSparseRawTick (encodeState)
open NumberedWindowInternalSparseRawTickNumericASTProof (emitValue)
open NumberedWindowInternalSparseRawRun (initialState)
open NumberedWindowInternalSparseRawRunTargets
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowPairAlgorithm (pair)

private theorem consValue (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

private abbrev row : Program 3 :=
  consOf (.projection 0) (consOf (.projection 1) (consOf (.projection 2) (constantZero 3)))

private theorem frameValue (q w r : Nat) :
    evaluate (.composition .succ (fun _ : Fin 1 => row)) (q ::ᵥ w ::ᵥ r ::ᵥ nil) =
      pack [q,w,r]+1 := by
  let xs := q ::ᵥ w ::ᵥ r ::ᵥ nil
  change Nat.succ (List.Vector.ofFn (fun _ : Fin 1 => evaluate row xs)).head = _
  rw [vectorOne]
  change Nat.succ (evaluate row xs) = _
  simp only [row,consValue,pack] <;> rfl

theorem initial : ExactOriginalRunInitialization := by
  intro q w r
  rw [initialState,emitValue,frameValue] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunInitialProof
