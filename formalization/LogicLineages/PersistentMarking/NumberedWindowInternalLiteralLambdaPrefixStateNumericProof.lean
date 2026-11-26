module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStateNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalLessThan (constantOne)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowInternalSparsePathEnvelope (applyUnary run cursor field)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (predEvaluation vectorOne)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof (vectorFive)
open NumberedWindowInternalSparseRawTick (emitState stateFrame rowBody)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (typedTape evalConsOf)

def typedFrameCode (c t q w r : Nat) : Nat := pack [c,t,q,w,r] + 1
def typedStateCode (flag frame : Nat) : Nat := pack [flag,frame]

theorem evalTypedFrame (c t q w r : Program 5) (xs : List.Vector Nat 5) :
    evaluate (prefixFrame c t q w r) xs =
      typedFrameCode (evaluate c xs) (evaluate t xs) (evaluate q xs) (evaluate w xs) (evaluate r xs) := by
  unfold prefixFrame
  rw [evaluate,vectorOne]
  change Nat.succ (evaluate _ xs) = _
  simp only [evalConsOf,typedFrameCode,pack]
  rfl

theorem evalTypedState {m : Nat} (flag frame : Program m) (xs : List.Vector Nat m) :
    evaluate (emitState flag frame) xs = typedStateCode (evaluate flag xs) (evaluate frame xs) := by
  simp only [emitState,evalConsOf,typedStateCode,pack]
  rfl

theorem stateHeadValue (flag frame : Nat) : run cellHead (typedStateCode flag frame) = flag :=
  (headTailOfCell (cellAt flag (pack [frame]))).1

theorem stateFrameValue (flag frame : Nat) : run stateFrame (typedStateCode flag frame) = frame := by
  have outer := (headTailOfCell (cellAt flag (pack [frame]))).2
  have last := (headTailOfCell (cellAt frame (pack []))).1
  simp only [stateFrame,field,cursor,typedStateCode,pack,applyValue] at *
  rw [outer,last]

theorem evalPrefixStart (c t q w r : Nat) :
    evaluate prefixStart (typedTape c t q w r) = typedStateCode 1 (typedFrameCode c t q w r) := by
  rw [prefixStart,evalTypedState,prefixInitialFrame,evalTypedFrame]
  rfl

private theorem readPrefixBody (flag c t q w r : Nat) :
    run rowBody (typedStateCode flag (typedFrameCode c t q w r)) = pack [c,t,q,w,r] := by
  rw [rowBody,applyValue,stateFrameValue]
  exact predEvaluation _

private theorem readAllSlots (flag c t q w r : Nat) :
    let n := typedStateCode flag (typedFrameCode c t q w r)
    run (prefixReadSlot 0) n = c ∧
      run (prefixReadSlot 1) n = t ∧
      run (prefixReadSlot 2) n = q ∧
      run (prefixReadSlot 3) n = w ∧ run (prefixReadSlot 4) n = r := by
  dsimp only
  have p := headTailOfCell (cellAt c (pack [t,q,w,r]))
  have q₀ := headTailOfCell (cellAt t (pack [q,w,r]))
  have r₀ := headTailOfCell (cellAt q (pack [w,r]))
  have w₀ := headTailOfCell (cellAt w (pack [r]))
  have v := headTailOfCell (cellAt r (pack []))
  simp only [prefixReadSlot,applyValue,readPrefixBody,cursor,pack] at *
  simp only [p.1,p.2,q₀.1,q₀.2,r₀.1,r₀.2,w₀.1,w₀.2,v.1,and_self]

theorem evalPrefixTickOnFrame (W : Program 3) (flag c t q w r : Nat) :
    run (prefixTick W) (typedStateCode flag (typedFrameCode c t q w r)) =
      evaluate (prefixLive W) (typedTape c t q w r) := by
  let n := typedStateCode flag (typedFrameCode c t q w r)
  have body : evaluate stateFrame (n ::ᵥ nil) = typedFrameCode c t q w r := stateFrameValue _ _
  have nonempty : typedFrameCode c t q w r ≠ 0 := by simp [typedFrameCode]
  unfold run
  rw [prefixTick,evalBranch,body,if_neg nonempty,prefixPerform,evaluate,vectorFive]
  obtain ⟨a,b,d,h,e⟩ := readAllSlots flag c t q w r
  change evaluate (prefixLive W)
    (run (prefixReadSlot 0) n ::ᵥ run (prefixReadSlot 1) n ::ᵥ run (prefixReadSlot 2) n ::ᵥ
      run (prefixReadSlot 3) n ::ᵥ run (prefixReadSlot 4) n ::ᵥ nil) = _
  rw [a,b,d,h,e]

theorem evalPrefixTickTerminal (W : Program 3) (flag : Nat) :
    run (prefixTick W) (typedStateCode flag 0) = typedStateCode flag 0 := by
  let n := typedStateCode flag 0
  have read : evaluate stateFrame (n ::ᵥ nil) = 0 := stateFrameValue _ _
  unfold run
  rw [prefixTick,evalBranch,read,if_pos rfl]
  rfl

#print axioms evalTypedFrame
#print axioms evalTypedState
#print axioms stateHeadValue
#print axioms stateFrameValue
#print axioms evalPrefixStart
#print axioms evalPrefixTickOnFrame
#print axioms evalPrefixTickTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStateNumericProof
