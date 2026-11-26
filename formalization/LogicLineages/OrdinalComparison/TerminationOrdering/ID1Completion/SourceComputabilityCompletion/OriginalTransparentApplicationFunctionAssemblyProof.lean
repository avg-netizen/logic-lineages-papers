module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionAssemblyProof
open UniformCertificateCompletion OriginalTransparentApplicationFunctionDefinitions
open OriginalTransparentApplicationFunctionTargets OriginalTransparentApplicationFunctionEvaluationProof
open OriginalHereditaryLambda (stateValues liveValue)
open OriginalHereditaryLambdaRawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Proof-only conditional assembly; guarded equality remains an explicit
supplier here, discharged only by a future concrete native theorem. -/
theorem transitionFromGuard (guarded : ActualGuardedEquality) : ActualTransitionEquality := by
 intro n arity p hp state
 rw [transitionEvaluation]
 by_cases h : evaluate (hopGuard p.base.oldSource) (stateValues state) = 1
 · rw [if_pos h,stateValuesLive]
   exact guarded n arity p hp (stateValues state) h
 · rw [if_neg h]

theorem oneStepFromTransition (trans : ActualTransitionEquality) : ActualOneStepEquality := by
 intro n arity p hp v
 rw [oneStepEvaluation,trans n arity p hp, stateValuesLive]

theorem calibrationFromEquality (he : ActualOneStepEquality) : ActualCalibration := by
 intro n arity p hp
 refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
 intro v
 exact (he n arity p hp v).trans (hp.2.2.2.2.1 v)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionAssemblyProof
