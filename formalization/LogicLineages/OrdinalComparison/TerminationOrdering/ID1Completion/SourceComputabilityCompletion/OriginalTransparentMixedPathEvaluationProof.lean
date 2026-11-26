module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathEvaluationProof
open OriginalTransparentMixedPathDefinitions
open OriginalHereditaryLambda (liveValue stateValues childValues matchingTargetValue lamPathValue)
open OriginalHereditaryLambdaRawProof OriginalHereditaryLambdaControlProof
open OriginalHereditaryLambdaEvaluationRepeatProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem transitionEvaluation (source : Program 2) (state : Nat) :
    evaluate (transition source) (List.Vector.ofFn ![state]) =
      if evaluate (OriginalTransparentLambdaStep.hopGuard source) (stateValues state) = 1
      then liveValue (childValues (stateValues state)) else evaluate (OriginalTransparentApplicationFunctionDefinitions.transition source) (List.Vector.ofFn ![state]) := by
  rw [transition,evalBranch,evalNormalize,atStateEvaluation,atStateEvaluation,childLiveEvaluation]
  by_cases h : evaluate (OriginalTransparentLambdaStep.hopGuard source) (stateValues state) = 1 <;> simp [h,evaluate]

theorem runEvaluation (source : Program 2) (v : List.Vector Nat 4) :
    evaluate (run source) v =
      repeatValue (transition source) (Nat.unpair (v.get 2)).1 (liveValue v) := by
  change evaluate (InternalRawListRepeat.repeatProgram (transition source))
    (List.Vector.ofFn fun i : Fin 2 => evaluate
      ((![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live] : Fin 2 → Program 4) i) v) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  change evaluate (InternalRawListRepeat.repeatProgram (transition source))
    (evaluate OriginalHereditaryLambda.path v ::ᵥ evaluate OriginalHereditaryLambda.live v ::ᵥ List.Vector.nil) = _
  rw [pathEvaluation,liveEvaluation]
  rfl

theorem refinedEvaluation (source : Program 2) (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (refined source oldStep) v =
      evaluate oldStep (stateValues
        (repeatValue (transition source) (Nat.unpair (v.get 2)).1 (liveValue v))) := by
  change evaluate (OriginalHereditaryLambda.atState oldStep)
    (List.Vector.ofFn fun _ : Fin 1 => evaluate (run source) v) = _
  rw [runEvaluation]
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  exact atStateEvaluation oldStep _

/-- Generic finite-iteration invariant, valid on every raw state, including
zero and malformed tuples. No successful guard or decoded path is assumed. -/
theorem repeatPreserves (source : Program 2) (f : Nat → Nat)
    (h : ∀ state, f (evaluate (transition source) (List.Vector.ofFn ![state])) = f state)
    (code state : Nat) : f (repeatValue (transition source) code state) = f state := by
  rw [repeatEvaluation]
  generalize ((NumberedMultisetNumeric.decodeNumbers code).getD []) = xs
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldr_cons]
    exact (h _).trans ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathEvaluationProof
