module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundRowsNumericProof
open NumberedWindowInternalLiteralSingletonBoundCalibrationProof (exact_LiteralBoundInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch singletonLambda)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpackNode)

/-- The contract a fallback slot actually needs: agreement with the
original singleton on tapes whose two operands pass the syntax test. -/
def GuardedDepthInstanceFit (U : Program 3) : Prop :=
  ∀ a d q, (syntaxBits a).1 = true → (syntaxBits q).1 = true →
    evaluate U (a ::ᵥ d ::ᵥ q ::ᵥ nil) = depthInstanceValue a d q

theorem exact_GuardedOfDepthInstanceFit (U : Program 3) (fit : DepthInstanceFit U) :
    GuardedDepthInstanceFit U :=
  fun a d q _ _ => fit a d q

/-- The physical atom and bound dispatch is calibrated on all inputs as
soon as its slot is calibrated behind the guard. The proof is the
existing bound calibration; the slot is consulted only after both
syntax bits are known. -/
theorem exact_LiteralSingletonBoundGuardedCalibration (V : Program 1) (H : Program 2) (U : Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U) :
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
      exact uFit a d q well qWell
    · rw [yes,if_neg (by decide : (1 : Nat) ≠ 0)]
      obtain ⟨ty,idx,shaped⟩ := (exact_LiteralBoundShape q).mp yes
      exact exact_LiteralBoundInstance H hFit a d q ty idx well qWell shaped

/-- The remaining numeric obligation for the lambda row, stated exactly:
a guarded fit of the written dispatch. It is not proved here. -/
theorem exact_LiteralSingletonLambdaCalibrationOfGuarded (V : Program 1) (H : Program 2) (U : Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H)
    (slotFit : GuardedDepthInstanceFit (singletonLambdaDispatch U)) :
    DepthInstanceFit (singletonLambda V H U) :=
  exact_LiteralSingletonBoundGuardedCalibration V H (singletonLambdaDispatch U) vFit hFit slotFit

#print axioms GuardedDepthInstanceFit
#print axioms exact_GuardedOfDepthInstanceFit
#print axioms exact_LiteralSingletonBoundGuardedCalibration
#print axioms exact_LiteralSingletonLambdaCalibrationOfGuarded
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
