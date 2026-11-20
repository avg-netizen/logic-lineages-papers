module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericASTProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorThree)
open InternalAcceptance (constantZero)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood field)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (atSlot tape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (witnessOne)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeTwo)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (firstField)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowRawContextAlgorithm (RawRoot)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)

theorem tagFiveOne (q w r : Nat) :
    evaluate tagFiveTest (tape q w r) = 1 ↔ ∃ child, unpackNode w = some (5,[child]) := by
  rw [tagFiveTest,atSlot]
  exact witnessOne w

theorem rootOne (q w r : Nat) :
    evaluate rootTest (tape q w r) = 1 ↔ ∃ payload, unpackNode w = some (0,[payload]) := by
  rw [rootTest,atSlot]
  change run (nodeGood (literal 1 0) 1) w = 1 ↔ _
  rw [nodeArity (literal 1 0) 1 w 0 (literalEvaluation 1 0 (w ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨payload,_ | ⟨later,rest⟩⟩ <;> simp at arity
    exact ⟨payload,h⟩
  · rintro ⟨payload,h⟩
    exact ⟨[payload],h,rfl⟩

private theorem nodeBit (tag : Program 1) (arity w : Nat) :
    run (nodeGood tag arity) w = 0 ∨ run (nodeGood tag arity) w = 1 := by
  unfold run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

theorem tagFiveZero (q w r : Nat) (absent : ¬ ∃ child, unpackNode w = some (5,[child])) :
    evaluate tagFiveTest (tape q w r) = 0 := by
  have bits : evaluate tagFiveTest (tape q w r) = 0 ∨ evaluate tagFiveTest (tape q w r) = 1 := by
    simp only [tagFiveTest,atSlot]
    change run (nodeGood (literal 1 5) 1) w = 0 ∨ run (nodeGood (literal 1 5) 1) w = 1
    exact nodeBit (literal 1 5) 1 w
  exact bits.resolve_right (fun h => absent ((tagFiveOne q w r).mp h))

theorem rootZero (q w r : Nat) (absent : ¬ ∃ child, unpackNode w = some (0,[child])) :
    evaluate rootTest (tape q w r) = 0 := by
  have bits : evaluate rootTest (tape q w r) = 0 ∨ evaluate rootTest (tape q w r) = 1 := by
    simp only [rootTest,atSlot]
    change run (nodeGood (literal 1 0) 1) w = 0 ∨ run (nodeGood (literal 1 0) 1) w = 1
    exact nodeBit (literal 1 0) 1 w
  exact bits.resolve_right (fun h => absent ((rootOne q w r).mp h))

theorem actualRootValue (root : RawRoot) (p : Program 3) (cal : ActualRoot root p)
    (q w r payload : Nat) (seen : unpackNode w = some (0,[payload])) :
    evaluate (rootCall p) (tape q w r) = (root q payload r).toNat := by
  let v := tape q w r
  rw [rootCall,evalNormalize]
  change (if evaluate p (List.Vector.ofFn (fun i : Fin 3 =>
    evaluate ((![.projection 0,frameSlot 0 1,.projection 2] : Fin 3 → Program 3) i) v)) = 1
    then 1 else 0) = _
  rw [vectorThree]
  change (if evaluate p (q ::ᵥ evaluate (frameSlot 0 1) v ::ᵥ r ::ᵥ nil) = 1 then 1 else 0) = _
  have payloadValue : run (field 0) w = payload := by
    rw [codeOfNode seen]
    exact firstField 0 payload []
  have atPayload : evaluate (frameSlot 0 1) v = payload := by
    rw [frameSlot,atSlot]
    exact payloadValue
  rw [atPayload,cal]
  cases root q payload r <;> rfl

private theorem consValue (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem emitValue (p q : Program 3) (v : List.Vector Nat 3) :
    evaluate (emitState p q) v = pack [evaluate p v,evaluate q v] := by
  simp only [emitState,consValue,pack] <;> rfl

theorem liveValue (root other : Program 3) (v : List.Vector Nat 3) :
    evaluate (liveTick root other) v =
      if evaluate tagFiveTest v = 0 then
        if evaluate rootTest v = 0 then pack [0,evaluate other v] else pack [evaluate (rootCall root) v,0]
      else pack [0,evaluate chosenFrame v] := by
  simp only [liveTick,evalBranch,emitValue] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericASTProof
