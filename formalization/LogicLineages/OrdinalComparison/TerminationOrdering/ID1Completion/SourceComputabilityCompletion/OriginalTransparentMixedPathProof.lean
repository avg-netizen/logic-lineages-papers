module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathProof
open UniformCertificateCompletion OriginalTransparentMixedPathDefinitions
open OriginalTransparentMixedPathTargets OriginalTransparentMixedPathEvaluationProof
open OriginalHereditaryLambda (liveValue stateValues)
open OriginalHereditaryLambdaRawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualTransitionEquality : ActualTransitionEquality := by
 intro n arity p hp state
 rw [transitionEvaluation]
 by_cases h : evaluate (OriginalTransparentLambdaStep.hopGuard p.base.oldSource) (stateValues state) = 1
 · rw [if_pos h]
   have hl := OriginalTransparentLambdaStepNativeProof.transitionPreserves n arity p hp state
   rw [OriginalTransparentLambdaStepEvaluationProof.transitionEvaluation,if_pos h] at hl
   exact hl
 · rw [if_neg h]
   exact OriginalTransparentApplicationFunctionCalibrationProof.actualTransitionEquality n arity p hp state

theorem actualOutputEquality : ActualOutputEquality := by
 intro n arity p hp v
 rw [refinedEvaluation]
 have h := repeatPreserves p.base.oldSource
   (fun state => evaluate p.oldStep (stateValues state))
   (actualTransitionEquality n arity p hp) (Nat.unpair (v.get 2)).1 (liveValue v)
 simpa only [stateValuesLive] using h

theorem actualCalibration : ActualCalibration := by
 intro n arity p hp
 refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
 intro v
 exact (actualOutputEquality n arity p hp v).trans (hp.2.2.2.2.1 v)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathProof
