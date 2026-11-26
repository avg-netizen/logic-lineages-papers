module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation vectorOne)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (evalBinaryComposition)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpackNode)

theorem exact_LiteralBoundInstance (H : Program 2) (hFit : ShiftHitFit H)
    (a d q ty idx : Nat) (well : (syntaxBits a).1 = true)
    (qWell : (syntaxBits q).1 = true) (shaped : unpackNode q = some (1,[ty,idx])) :
    evaluate (boundInstance H) (tape a d q) = depthInstanceValue a d q := by
  have qType : (syntaxBits q).1 = NumberedWindowAddressAlgorithm.typeBit ty := by
    simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,shaped,Option.any_some,
      NumberedWindowSyntaxAlgorithm.termParts]
  have t := qType.symm.trans qWell
  have slot : evaluate boundIndex (tape a d q) = idx := by
    rw [boundIndex,atSlot]
    exact (exact_LiteralBoundFields q ty idx shaped).2
  have cost : evaluate (.projection (1 : Fin 3)) (tape a d q) = d := rfl
  have below : evaluate boundBeforeDepth (tape a d q) = (if idx < d then 1 else 0) := by
    rw [boundBeforeDepth,evalBinaryComposition,slot,cost,exactLessThanEvaluation]
  have matchHere : evaluate boundAtDepth (tape a d q) = (if idx = d then 1 else 0) := by
    rw [boundAtDepth,evalBinaryComposition,slot,cost,exactEqualityEvaluation]
  rw [depthInstanceValue,exact_OriginalSingletonBound a d q ty idx shaped,well,t]
  change _ = (if idx < d then q else if idx = d then
    ((NumberedWindowShiftAlgorithm.output d 0 a).1).getD 0 else NumberedWindowFieldAlgorithm.packNode 1 [ty,idx.pred]) + 1
  rw [boundInstance,evalBranch,below]
  by_cases pos : idx < d
  · simp only [if_pos pos,if_neg (by decide : (1 : Nat) ≠ 0)]
    rw [retainSingleton,evaluate,vectorOne]
    rfl
  · simp only [if_neg pos,if_true]
    rw [evalBranch,matchHere]
    by_cases eq : idx = d
    · simp only [if_pos eq,if_neg (by decide : (1 : Nat) ≠ 0)]
      rw [exact_LiteralShiftedInsertion H hFit a d q well]
      rfl
    · simp only [if_neg eq,if_true]
      exact exact_LiteralBoundLowered a d q ty idx shaped

theorem exact_LiteralSingletonBoundCalibration (V : Program 1) (H : Program 2) (U : Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (uFit : DepthInstanceFit U) :
    DepthInstanceFit (singletonBound V H U) := by
  apply exact_LiteralSingletonAtomsCalibration V _ vFit
  intro a d q
  change evaluate (branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)) (tape a d q) = _
  rw [evalBranch,exact_LiteralSingletonSyntaxBit V vFit]
  cases both : ((syntaxBits a).1 && (syntaxBits q).1) with
  | false =>
    simp only [Bool.toNat_false]
    simp only [depthInstanceValue,NumberedWindowSingletonAlgorithm.output,both]
    rfl
  | true =>
    simp only [Bool.and_eq_true] at both
    obtain ⟨well,qWell⟩ := both
    simp only [Bool.toNat_true,show (1 : Nat) ≠ 0 by decide,if_false]
    rw [singletonBoundDispatch,evalBranch,atSlot]
    change (if NumberedWindowInternalSparsePathEnvelope.run boundShape q = 0 then evaluate U (tape a d q)
      else evaluate (boundInstance H) (tape a d q)) = _
    rcases exact_LiteralBoundShapeBit q with no | yes
    · rw [no,if_pos rfl]
      exact uFit a d q
    · rw [yes,if_neg (by decide : (1 : Nat) ≠ 0)]
      obtain ⟨ty,idx,shaped⟩ := (exact_LiteralBoundShape q).mp yes
      exact exact_LiteralBoundInstance H hFit a d q ty idx well qWell shaped

#print axioms exact_LiteralBoundInstance
#print axioms exact_LiteralSingletonBoundCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundCalibrationProof
