module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowFieldAlgorithm (pack)

abbrev tape (q w r : Nat) : List.Vector Nat 3 := q ::ᵥ w ::ᵥ r ::ᵥ nil

theorem atSlot (p : Program 1) (i : Fin 3) (v : List.Vector Nat 3) :
    evaluate (onRaw p i) v = run p (v.get i) := by
  change evaluate p (List.Vector.ofFn (fun _ : Fin 1 =>
    evaluate (.projection i) v)) = _
  rw [vectorOne]
  rfl

theorem sameSlotOne (n : Nat) (v : List.Vector Nat 3) :
    evaluate (sameSlot n) v = 1 ↔ run (field n) (v.get 0) = run (field n) (v.get 2) := by
  change evaluate equalityTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![frameSlot n 0,frameSlot n 2] : Fin 2 → Program 3) i) v)) = 1 ↔ _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate (frameSlot n 0) v ::ᵥ evaluate (frameSlot n 2) v ::ᵥ nil) = 1 ↔ _
  rw [exactEqualityEvaluation]
  simp only [frameSlot,atSlot]
  split <;> simp_all

private theorem bothOne {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (conjunction p q) v = 1 ↔ evaluate p v = 1 ∧ evaluate q v = 1 := by
  rw [conjunctionEvaluation]
  split <;> simp_all

theorem guardOne (q w r : Nat) :
    evaluate frameGood (tape q w r) = 1 ↔
      run witnessShape w = 1 ∧ run termShape q = 1 ∧ run termShape r = 1 ∧
        run (field 0) q = run (field 0) r ∧
        run (field 1) q = run (field 1) r ∧
        run (field 3) q = run (field 3) r := by
  simp only [frameGood,bothOne,atSlot,sameSlotOne] <;> rfl

theorem guardBit (v : List.Vector Nat 3) :
    evaluate frameGood v = 0 ∨ evaluate frameGood v = 1 := by
  unfold frameGood
  rw [conjunctionEvaluation]
  split <;> simp

private theorem consValue (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

private theorem emitValue (q w r : Nat) :
    evaluate emitFrame (tape q w r) =
      encodeFrame (some (run (field 2) q,run (field 0) w,run (field 2) r)) := by
  let b := consOf (frameSlot 2 0) (consOf (frameSlot 0 1) (consOf (frameSlot 2 2) (constantZero 3)))
  change Nat.succ (List.Vector.ofFn (fun _ : Fin 1 =>
    evaluate b (tape q w r))).head = _
  rw [vectorOne]
  change Nat.succ (evaluate b (tape q w r)) = _
  simp only [b,consValue,frameSlot,atSlot,encodeFrame,pack] <;> rfl

theorem value (q w r : Nat) :
    evaluate chosenFrame (tape q w r) =
      if evaluate frameGood (tape q w r) = 0 then 0
      else encodeFrame (some (run (field 2) q,run (field 0) w,run (field 2) r)) := by
  rw [chosenFrame,evalBranch,emitValue] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
