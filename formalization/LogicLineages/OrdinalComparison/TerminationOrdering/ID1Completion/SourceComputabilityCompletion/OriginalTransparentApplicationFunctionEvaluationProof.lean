module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionEvaluationProof
open OriginalTransparentApplicationFunctionDefinitions
open OriginalHereditaryLambda (liveValue stateValues)
open OriginalHereditaryLambdaRawProof OriginalHereditaryLambdaControlProof
open OriginalHereditaryLambdaEvaluationRepeatProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def childValues (v : List.Vector Nat 4) : List.Vector Nat 4 :=
 List.Vector.ofFn ![evaluate sourceFunction v,evaluate targetFunction v,evaluate childCertificate v,v.get 3]

theorem childLiveEvaluation (v : List.Vector Nat 4) : evaluate childLive v = liveValue (childValues v) := by
 change evaluate OriginalHereditaryLambda.live (childValues v) = _
 exact liveEvaluation _

theorem hopGuardEvaluation (source : Program 2) (v : List.Vector Nat 4) :
 evaluate (hopGuard source) v =
  if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧ evaluate structuralGuard v = 1 then 1 else 0 := by
 rw [hopGuard,conjunctionEvaluation]
 rfl

theorem transitionEvaluation (source : Program 2) (state : Nat) :
 evaluate (transition source) (List.Vector.ofFn ![state]) =
 if evaluate (hopGuard source) (stateValues state) = 1 then liveValue (childValues (stateValues state)) else state := by
 rw [transition,evalBranch,evalNormalize,atStateEvaluation,atStateEvaluation,childLiveEvaluation]
 by_cases h : evaluate (hopGuard source) (stateValues state) = 1 <;> simp [h,evaluate]

theorem oneStepEvaluation (source : Program 2) (oldStep : Program 4) (v : List.Vector Nat 4) :
 evaluate (oneStep source oldStep) v =
 evaluate oldStep (stateValues (evaluate (transition source) (List.Vector.ofFn ![liveValue v]))) := by
 change evaluate (OriginalHereditaryLambda.atState oldStep)
   (List.Vector.ofFn fun _ : Fin 1 => evaluate (transition source)
    (List.Vector.ofFn fun _ : Fin 1 => evaluate OriginalHereditaryLambda.live v)) = _
 rw [liveEvaluation]
 rw [InternalEqualityTestEvaluationProof.vectorOne]
 exact atStateEvaluation oldStep _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionEvaluationProof
