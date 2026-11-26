module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStateNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedChildNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStepNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot sameSlotOne)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralLambdaFrameProof
open NumberedWindowInternalLiteralLambdaLexicalGateProof
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixStateNumericProof

theorem evalRawTripleCall (p : Program 3) (c t q w r : Nat) :
    evaluate (rawTripleCall p) (typedTape c t q w r) = evaluate p (tape q w r) := by
  rw [rawTripleCall,evalTernaryComposition]
  rfl

theorem evalLambdaPrefixBit (c t q w r : Nat) :
    evaluate isLambdaPrefix (typedTape c t q w r) = 0 ∨ evaluate isLambdaPrefix (typedTape c t q w r) = 1 := by
  rw [isLambdaPrefix,conjunctionEvaluation]
  split <;> simp

theorem evalLambdaPrefixWitness (c t q w r : Nat)
    (accepted : evaluate isLambdaPrefix (typedTape c t q w r) = 1) :
    ∃ child, unpackNode w = some (1,[child]) := by
  rw [isLambdaPrefix,conjunctionOne,evalRawTripleCall,evalRawTripleCall] at accepted
  have h := accepted.2
  have slot := atSlot lambdaWitnessShape 1 (tape q w r)
  rw [lambdaWitnessTest,slot] at h
  change run lambdaWitnessShape w = 1 at h
  rw [lambdaWitnessShape,nodeArity _ 1 w 1 (literalEvaluation 1 1 (w ::ᵥ nil))] at h
  obtain ⟨fs,seen,len⟩ := h
  rcases fs with _ | ⟨a,_ | ⟨b,bs⟩⟩ <;> simp at len
  exact ⟨a,seen⟩

set_option maxHeartbeats 1200000
private theorem evalLambdaFrames (q w r d a b : Nat)
    (src : unpackNode q = some (2,[d,a])) (dest : unpackNode r = some (2,[d,b])) :
    evaluate lambdaFrameGuard (tape q w r) = 1 := by
  simp only [lambdaFrameGuard,conjunctionOne,atSlot,sameSlotOne]
  change run rawLambdaShape q = 1 ∧ run rawLambdaShape r = 1 ∧ run (field 0) q = run (field 0) r
  have yes (input d a : Nat) (h : unpackNode input = some (2,[d,a])) : run rawLambdaShape input = 1 := by
    rw [rawLambdaShape,nodeArity _ 2 input 2 (literalEvaluation 1 2 (input ::ᵥ nil))]
    exact ⟨[d,a],h,rfl⟩
  exact ⟨yes q d a src, yes r d b dest,
    (evalLiteralLambdaFields q d a src).1.trans (evalLiteralLambdaFields r d b dest).1.symm⟩

private theorem evalWitnessBody (w child : Nat) (h : unpackNode w = some (1,[child])) : run (field 0) w = child := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 1 (pack [child]))).2
  have inner : run cellHead (pack [child]) = child := (headTailOfCell (cellAt child (pack []))).1
  change run (field 0) (pair 1 (pack [child]) + 1) = child
  simp only [field,cursor,applyValue,outer,inner]

/-- The real prefix machine pays the two child windows at the pushed
context, and writes the exact next typed tape and smaller certificate. -/
theorem evalLambdaPrefixLiveGood (W : Program 3) (s : Settings) (fit : ActualPackedWindow s W)
    (c t q w r d a child b cod : Nat)
    (isLambda : evaluate isLambdaPrefix (typedTape c t q w r) = 1)
    (source : unpackNode q = some (2,[d,a])) (dest : unpackNode r = some (2,[d,b]))
    (witness : unpackNode w = some (1,[child])) (type : t = arrow d cod)
    (left : packedWindow s (pair d c + 1) cod a = true)
    (right : packedWindow s (pair d c + 1) cod b = true) :
    evaluate (prefixLive W) (typedTape c t q w r) =
      typedStateCode 1 (typedFrameCode (pair d c + 1) cod a child b) := by
  subst t
  let v := typedTape c (arrow d cod) q w r
  have test : evaluate (prefixValidation W) v = 1 := by
    rw [prefixValidation,conjunctionOne,evalRawTripleCall]
    exact ⟨evalLambdaFrames q w r d a b source dest,
      exact_LiteralLexicalGateEvaluates W s fit c (arrow d cod) q w r d a b cod source dest rfl left right⟩
  have dRead : evaluate lexicalBinder v = d := by rw [lexicalBinder,evalLexicalSlot]; exact (evalLiteralLambdaFields q d a source).1
  have push : evaluate lexicalContext v = pair d c + 1 := by rw [lexicalContext,evalConsOf,dRead]; rfl
  have kRead : evaluate lexicalCodomain v = cod := by rw [lexicalCodomain,evalLexicalSlot]; exact (headTailOfCell (cellAt d cod)).2
  have aRead : evaluate lexicalSourceBody v = a := by rw [lexicalSourceBody,evalLexicalSlot]; exact (evalLiteralLambdaFields q d a source).2
  have bRead : evaluate lexicalTargetBody v = b := by rw [lexicalTargetBody,evalLexicalSlot]; exact (evalLiteralLambdaFields r d b dest).2
  have kid : evaluate prefixInnerWitness v = child := by rw [prefixInnerWitness,evalLexicalSlot]; exact evalWitnessBody w child witness
  rw [prefixLive,evalBranch,isLambda,if_neg (by decide : (1 : Nat) ≠ 0)]
  rw [evalBranch,show evaluate (prefixValidation W) (typedTape c (arrow d cod) q w r) = 1 from test,if_neg (by decide : (1 : Nat) ≠ 0)]
  rw [evalTypedState,prefixNext,evalTypedFrame]
  change typedStateCode 1 (typedFrameCode (evaluate lexicalContext v) (evaluate lexicalCodomain v)
    (evaluate lexicalSourceBody v) (evaluate prefixInnerWitness v) (evaluate lexicalTargetBody v)) = _
  rw [push,kRead,aRead,kid,bRead]

theorem evalLambdaPrefixLiveStop (W : Program 3) (c t q w r : Nat)
    (done : evaluate isLambdaPrefix (typedTape c t q w r) = 0) :
    evaluate (prefixLive W) (typedTape c t q w r) = typedStateCode 1 0 := by
  rw [prefixLive,evalBranch,done,if_pos rfl,prefixAccept,evalTypedState]
  rfl

#print axioms evalRawTripleCall
#print axioms evalLambdaPrefixBit
#print axioms evalLambdaPrefixWitness
#print axioms evalLambdaPrefixLiveGood
#print axioms evalLambdaPrefixLiveStop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStepNumericProof
