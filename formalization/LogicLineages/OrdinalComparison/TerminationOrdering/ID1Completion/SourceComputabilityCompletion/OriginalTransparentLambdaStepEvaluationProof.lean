module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepEvaluationProof
open OriginalTransparentLambdaStep
open OriginalHereditaryLambda (liveValue stateValues childValues matchingTargetValue lamPathValue)
open OriginalHereditaryLambdaRawProof OriginalHereditaryLambdaControlProof
open OriginalHereditaryLambdaEvaluationRepeatProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only literal guard evaluation; false means complete state identity. -/
theorem hopGuardEvaluation (source : Program 2) (v : List.Vector Nat 4) :
    evaluate (hopGuard source) v =
      if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1 ∧
        matchingTargetValue v = 1 ∧ lamPathValue v = 1 then 1 else 0 := by
  have hs : evaluate (OriginalTransparentVariableStep.sourceAt source) v =
      evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) := rfl
  rw [hopGuard,conjunctionEvaluation,conjunctionEvaluation,conjunctionEvaluation,
    hs,matchingTargetEvaluation,lamPathEvaluation]
  by_cases hs : evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 <;>
    by_cases hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1 <;>
      by_cases hm : matchingTargetValue v = 1 <;>
        by_cases hp : lamPathValue v = 1 <;> simp [hs,hl,hm,hp]

theorem transitionEvaluation (source : Program 2) (state : Nat) :
    evaluate (transition source) (List.Vector.ofFn ![state]) =
      if evaluate (hopGuard source) (stateValues state) = 1
      then liveValue (childValues (stateValues state)) else state := by
  rw [transition,evalBranch,evalNormalize,atStateEvaluation,atStateEvaluation,childLiveEvaluation]
  by_cases h : evaluate (hopGuard source) (stateValues state) = 1 <;> simp [h,evaluate]

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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepEvaluationProof
