module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericLiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericStateProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (vectorThree)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowRawContextAlgorithm (tick)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (predEvaluation)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets
open NumberedWindowInternalSparseRawTickNumericLiveProof (live)

private theorem frameRead (flag frame : Nat) : run stateFrame (pack [flag,frame]) = frame := by
  have tail : run cellTail (pack [flag,frame]) = pack [frame] :=
    (headTailOfCell (cellAt flag (pack [frame]))).2
  have head : run cellHead (pack [frame]) = frame :=
    (headTailOfCell (cellAt frame (pack []))).1
  simp only [stateFrame,field,cursor,applyValue,tail,head]

private theorem bodyRead (flag q w r : Nat) :
    run rowBody (pack [flag,pack [q,w,r]+1]) = pack [q,w,r] := by
  rw [rowBody,applyValue,frameRead] <;> exact predEvaluation (pack [q,w,r]+1)

private theorem rowRead (flag q w r : Nat) :
    let n := pack [flag,pack [q,w,r]+1]
    run rowSource n = q ∧ run rowWitness n = w ∧ run rowDestination n = r := by
  have q0 : run cellHead (pack [q,w,r]) = q ∧ run cellTail (pack [q,w,r]) = pack [w,r] :=
    headTailOfCell (cellAt q (pack [w,r]))
  have w0 : run cellHead (pack [w,r]) = w ∧ run cellTail (pack [w,r]) = pack [r] :=
    headTailOfCell (cellAt w (pack [r]))
  have r0 : run cellHead (pack [r]) = r := (headTailOfCell (cellAt r (pack []))).1
  have rest := bodyRead flag q w r
  exact ⟨by simp only [rowSource,applyValue,rest,q0.1],
    by simp only [rowWitness,applyValue,rest,q0.2,w0.1],
    by simp only [rowDestination,applyValue,rest,q0.2,w0.2,r0]⟩

private theorem activeValue (p other : Program 3) (flag q w r : Nat) :
    evaluate (performLive p other) (pack [flag,pack [q,w,r]+1] ::ᵥ nil) =
      evaluate (liveTick p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) := by
  let n := pack [flag,pack [q,w,r]+1]
  change evaluate (liveTick p other) (List.Vector.ofFn (fun i : Fin 3 =>
    evaluate ((![rowSource,rowWitness,rowDestination] : Fin 3 → Program 1) i) (n ::ᵥ nil))) = _
  rw [vectorThree]
  change evaluate (liveTick p other)
    (run rowSource n ::ᵥ run rowWitness n ::ᵥ run rowDestination n ::ᵥ nil) = _
  obtain ⟨hq,hw,hr⟩ := rowRead flag q w r
  rw [hq,hw,hr]

theorem encoded : ExactOriginalEncodedTick := by
  intro root p other hp ho s
  rcases s with ⟨flag,_ | ⟨q,w,r⟩⟩
  · rw [chosenTick,evalBranch]
    change (if run stateFrame (pack [flag.toNat,0]) = 0 then pack [flag.toNat,0] else _) =
      pack [flag.toNat,0]
    rw [frameRead,if_pos rfl]
  · rw [chosenTick,evalBranch]
    change (if run stateFrame (pack [flag.toNat,pack [q,w,r]+1]) = 0 then _ else
      evaluate (performLive p other) (pack [flag.toNat,pack [q,w,r]+1] ::ᵥ nil)) = _
    rw [frameRead,if_neg (Nat.succ_ne_zero _),activeValue]
    exact live root p other hp ho flag q w r

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericStateProof
