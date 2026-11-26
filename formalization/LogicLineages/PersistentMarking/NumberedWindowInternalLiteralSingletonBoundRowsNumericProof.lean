module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowShiftChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingBaseProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation vectorOne)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation predEvaluation)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (evalConsOf evalBinaryComposition)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (retainSingleton)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowFieldAlgorithm (unpackNode pack packNode)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowArithmeticTermCode (decodeTerm)
open NumberedWindowArithmeticTermCodeChecks (exact_TermCodec)
open NumberedWindowArithmeticSyntaxAlgorithmChecks (exact_ExactTermArgsGuards)
open NumberedWindowArithmeticSyntaxAlgorithmTargets (OriginalRow)
open NumberedWindowShiftChecks (exact_ShiftOutput)
open NumberedWindowBindingBaseProof (shiftZero)

theorem exact_LiteralBoundShapeBit (q : Nat) : run boundShape q = 0 ∨ run boundShape q = 1 := by
  unfold run boundShape nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

theorem exact_LiteralBoundShape (q : Nat) :
    run boundShape q = 1 ↔ ∃ ty i, unpackNode q = some (1,[ty,i]) := by
  rw [boundShape,nodeArity _ 2 q 1 (literalEvaluation 1 1 _)]
  constructor
  · rintro ⟨fs,report,len⟩
    rcases fs with _ | ⟨ty,_ | ⟨idx,_ | ⟨last,more⟩⟩⟩ <;> simp at len
    exact ⟨ty,idx,report⟩
  · rintro ⟨ty,idx,h⟩
    exact ⟨[ty,idx],h,rfl⟩

theorem exact_LiteralBoundFields (q ty i : Nat) (h : unpackNode q = some (1,[ty,i])) :
    run (field 0) q = ty ∧ run (field 1) q = i := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 1 (pack [ty,i]))).2
  have inner : run cellHead (pack [ty,i]) = ty ∧ run cellTail (pack [ty,i]) = pack [i] :=
    headTailOfCell (cellAt ty (pack [i]))
  have final : run cellHead (pack [i]) = i := (headTailOfCell (cellAt i (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 1 (pack [ty,i]) + 1) = ty ∧ _
  simp only [field,cursor,applyValue,packNode,outer,inner.1,inner.2,final] <;> simp

theorem exact_LiteralBoundLowered (a d q ty i : Nat) (h : unpackNode q = some (1,[ty,i])) :
    evaluate boundLowered (tape a d q) = packNode 1 [ty,i.pred] + 1 := by
  obtain ⟨t,x⟩ := exact_LiteralBoundFields q ty i h
  rw [boundLowered,evaluate,vectorOne]
  change evaluate boundLowerCode (tape a d q) + 1 = _
  rw [boundLowerCode,evalConsOf,evalConsOf,evalConsOf,literalEvaluation,boundType,loweredIndex,atSlot,atSlot]
  change NumberedWindowPairAlgorithm.pair 1
    (NumberedWindowPairAlgorithm.pair (run (field 0) q)
      (NumberedWindowPairAlgorithm.pair (run (NumberedWindowInternalSparsePathEnvelope.applyUnary
        NumberedWindowInternalFreshProbeDispatchProgram.predOne (field 1)) q) 0 + 1) + 1) + 1 + 1 = _
  have pr : run NumberedWindowInternalFreshProbeDispatchProgram.predOne i = i.pred := predEvaluation i
  rw [t,applyValue,x,pr]
  rfl

theorem exact_ShiftHitAtZero (a : Nat) (well : (syntaxBits a).1 = true) :
    shiftHitValue a 0 = a + 1 := by
  rw [exact_ExactTermArgsGuards a] at well
  change (decodeTerm a).isSome = true at well
  cases found : decodeTerm a with
  | none => simp [found] at well
  | some q =>
    have code := (exact_TermCodec.1 a q).mp found
    rw [shiftHitValue,exact_ShiftOutput,found]
    simp only [Option.map_some,Option.getD_some,shiftZero,code]

theorem exact_LiteralShiftedInsertion (H : Program 2) (fit : ShiftHitFit H)
    (a d q : Nat) (well : (syntaxBits a).1 = true) :
    evaluate (shiftedInsertion H) (tape a d q) = shiftHitValue a d := by
  rw [shiftedInsertion,evalBranch]
  change (if d = 0 then evaluate directInsertion (tape a d q)
      else evaluate (.composition H ![.projection 0,.projection 1]) (tape a d q)) = _
  by_cases zero : d = 0
  · subst d
    rw [if_pos rfl,directInsertion,evaluate,vectorOne,exact_ShiftHitAtZero a well]
    rfl
  · rw [if_neg zero,evalBinaryComposition]
    exact fit a d

#print axioms exact_LiteralBoundShapeBit
#print axioms exact_LiteralBoundShape
#print axioms exact_LiteralBoundFields
#print axioms exact_LiteralBoundLowered
#print axioms exact_ShiftHitAtZero
#print axioms exact_LiteralShiftedInsertion
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
