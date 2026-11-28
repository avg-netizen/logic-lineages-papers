module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
  (DepthInstanceFit zeroDepthInstance exact_ZeroDepthInstance exact_LiteralDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
  (ShiftHitFit singletonBound exact_LiteralShiftHit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
  (GuardedDepthInstanceFit exact_GuardedOfDepthInstanceFit
    exact_LiteralSingletonBoundGuardedCalibration)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaChildFitProof
  (exact_LiteralSingletonLambdaCalibrationOfFallback)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
  (shiftHitLiterals exact_ShiftHitLiteralsFit)

/-- The shift and fallback programs are chosen before the syntax program.
For every calibrated syntax program the written lambda instance over
them is calibrated at all depths, and its depth-zero wrapper is a beta
instance. No hypothesis remains. -/
theorem exact_SingletonLambdaInstanceConstructor :
    ∃ (H : Program 2) (U : Program 3), ShiftHitFit H ∧ DepthInstanceFit U ∧
      ∀ Vs : Program 1, ActualRawSyntax Vs →
        DepthInstanceFit (singletonLambda Vs H U) ∧
        InstanceFit (zeroDepthInstance (singletonLambda Vs H U)) := by
  obtain ⟨H,hFit⟩ := exact_LiteralShiftHit
  obtain ⟨U,uFit⟩ := exact_LiteralDepthInstance
  refine ⟨H,U,hFit,uFit,fun Vs vFit => ?_⟩
  have fit := exact_LiteralSingletonLambdaCalibrationOfFallback Vs H U vFit hFit
    (exact_GuardedOfDepthInstanceFit U uFit)
  exact ⟨fit,exact_ZeroDepthInstance (singletonLambda Vs H U) fit⟩

/-- The lambda program with the literal shift front and bound fallback is
calibrated at every depth using the same syntax program for both slots. -/
theorem exact_SingletonLambdaLiteralsDepthFit (H : Program 2) (U : Program 3)
    (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U)
    (Vs : Program 1) (vFit : ActualRawSyntax Vs) :
    DepthInstanceFit (singletonLambda Vs (shiftHitLiterals Vs H)
      (singletonBound Vs (shiftHitLiterals Vs H) U)) := by
  have shiftFit := exact_ShiftHitLiteralsFit Vs H vFit hFit
  have slotFit : GuardedDepthInstanceFit (singletonBound Vs (shiftHitLiterals Vs H) U) :=
    exact_GuardedOfDepthInstanceFit _
      (exact_LiteralSingletonBoundGuardedCalibration Vs (shiftHitLiterals Vs H) U vFit shiftFit uFit)
  exact exact_LiteralSingletonLambdaCalibrationOfFallback Vs (shiftHitLiterals Vs H)
    (singletonBound Vs (shiftHitLiterals Vs H) U) vFit shiftFit slotFit

/-- The literal shift front and bound fallback give the beta instance at depth zero. -/
theorem exact_SingletonLambdaLiteralsInstanceFit (H : Program 2) (U : Program 3)
    (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U)
    (Vs : Program 1) (vFit : ActualRawSyntax Vs) :
    InstanceFit (zeroDepthInstance (singletonLambda Vs (shiftHitLiterals Vs H)
      (singletonBound Vs (shiftHitLiterals Vs H) U))) := by
  exact exact_ZeroDepthInstance _
    (exact_SingletonLambdaLiteralsDepthFit H U hFit uFit Vs vFit)

/-- Choose the shift and fallback seeds before selecting the syntax program,
and calibrate the literal lambda program and its depth-zero instance. -/
theorem exact_SingletonLambdaLiteralsInstanceConstructor :
    ∃ (H : Program 2) (U : Program 3), ShiftHitFit H ∧ DepthInstanceFit U ∧
      ∀ Vs : Program 1, ActualRawSyntax Vs →
        DepthInstanceFit (singletonLambda Vs (shiftHitLiterals Vs H)
          (singletonBound Vs (shiftHitLiterals Vs H) U)) ∧
        InstanceFit (zeroDepthInstance (singletonLambda Vs (shiftHitLiterals Vs H)
          (singletonBound Vs (shiftHitLiterals Vs H) U))) := by
  obtain ⟨H,hFit⟩ := exact_LiteralShiftHit
  obtain ⟨U,uFit⟩ := exact_LiteralDepthInstance
  refine ⟨H,U,hFit,uFit,fun Vs vFit => ?_⟩
  have fit := exact_SingletonLambdaLiteralsDepthFit H U hFit
    (exact_GuardedOfDepthInstanceFit U uFit) Vs vFit
  exact ⟨fit,exact_ZeroDepthInstance _ fit⟩

#print axioms exact_SingletonLambdaInstanceConstructor
#print axioms exact_SingletonLambdaLiteralsDepthFit
#print axioms exact_SingletonLambdaLiteralsInstanceFit
#print axioms exact_SingletonLambdaLiteralsInstanceConstructor
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
