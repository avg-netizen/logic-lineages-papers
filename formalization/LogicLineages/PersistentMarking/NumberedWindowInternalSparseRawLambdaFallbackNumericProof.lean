module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFallbackNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback)
open NumberedWindowInternalSparseRawTick (fallbackValue)
open NumberedWindowInternalSparseRawLambdaFrame
open NumberedWindowInternalSparseRawLambdaFrameNumericProof (exact_AllRawLambdaFrame)
open NumberedWindowInternalSparseRawLambdaRun

private theorem guardHit (q w r : Nat) :
    evaluate lambdaTest (tape q w r) = 1 ↔ ∃ child, unpackNode w = some (1,[child]) := by
  rw [lambdaTest,atSlot]
  change run (nodeGood (literal 1 1) 1) w = 1 ↔ _
  rw [nodeArity (literal 1 1) 1 w 1 (literalEvaluation 1 1 (w ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨child,_ | ⟨later,rest⟩⟩ <;> simp at arity
    exact ⟨child,h⟩
  · rintro ⟨child,h⟩
    exact ⟨[child],h,rfl⟩

private theorem guardBit (q w r : Nat) :
    evaluate lambdaTest (tape q w r) = 0 ∨ evaluate lambdaTest (tape q w r) = 1 := by
  rw [lambdaTest,atSlot]
  change run (nodeGood (literal 1 1) 1) w = 0 ∨ run (nodeGood (literal 1 1) 1) w = 1
  unfold run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

/-- The selected new physical fallback has the original complete
numeric table, from the original fallback fit already supplied. -/
theorem exact_LambdaFallbackFit : ExactLambdaFallbackFit := by
  intro other old q w r
  change evaluate (lambdaFallback other) (tape q w r) = _
  rw [lambdaFallback,evalBranch]
  by_cases hit : ∃ child, unpackNode w = some (1,[child])
  · obtain ⟨child,hw⟩ := hit
    have test := (guardHit q w r).mpr ⟨child,hw⟩
    rw [test,if_neg (by decide : (1 : Nat) ≠ 0)]
    rw [exact_AllRawLambdaFrame]
    simp [tagOneNext,fallbackValue,hw]
  · have test := (guardBit q w r).resolve_right (fun y => hit ((guardHit q w r).mp y))
    rw [test,if_pos rfl]
    exact old q w r

#print axioms exact_LambdaFallbackFit
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFallbackNumericProof
