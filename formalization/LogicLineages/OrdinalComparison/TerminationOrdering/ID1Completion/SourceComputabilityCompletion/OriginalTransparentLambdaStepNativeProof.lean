module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeProof
open UniformCertificateCompletion OriginalTransparentLambdaStep OriginalTransparentLambdaStepTargets
open OriginalHereditaryLambda (stateValues liveValue childValues matchingTargetValue lamPathValue)
open OriginalHereditaryLambdaRawProof
open OriginalTransparentLambdaStepEvaluationProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both Boolean outcomes are proved, not only preservation of accepted
certificates. Malformed/rejected child tails therefore cannot create a hit. -/
theorem leafEquality (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1)
    (hm : matchingTargetValue v = 1) (hp : lamPathValue v = 1) :
    leafValue n arity (childValues v) = leafValue n arity v := by
  rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hzero | hone
  · rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity (childValues v) with hc | hc
    · exact hc.trans hzero.symm
    · have hparent := OriginalTransparentLambdaStepNativeLiftProof.leafParentAccept
        n arity v hs hl hm hp hc
      omega
  · exact (OriginalTransparentLambdaStepNativeForwardProof.leafChildAccept
      n arity oldStep hcal v hl hm hone).trans hone.symm

/-- One transition preserves the numeric result on EVERY state, even zero.
The inactive branch retains the whole state, not merely acceptance. -/
theorem transitionPreserves (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (state : Nat) :
    evaluate p.oldStep (stateValues
      (evaluate (transition p.base.oldSource) (List.Vector.ofFn ![state]))) =
      evaluate p.oldStep (stateValues state) := by
  rw [transitionEvaluation]
  by_cases ha : evaluate (hopGuard p.base.oldSource) (stateValues state) = 1
  · rw [if_pos ha,stateValuesLive]
    have h := ha
    rw [hopGuardEvaluation] at h
    have hf : evaluate p.base.oldSource
        (List.Vector.ofFn ![(stateValues state).get 0,(stateValues state).get 3]) = 1 ∧
        evaluate OriginalLambdaGuardLeaf.sourceLambda (stateValues state) = 1 ∧
        matchingTargetValue (stateValues state) = 1 ∧ lamPathValue (stateValues state) = 1 := by
      split at h
      next htrue => exact htrue
      next => contradiction
    rw [hp.1.1] at hf
    rw [hp.2.2.2.2.1,hp.2.2.2.2.1]
    exact leafEquality n arity p.oldStep hp.2.2.2.2.1 (stateValues state)
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  · rw [if_neg ha]

theorem actualOriginalTransparentLambdaStepEquality : ActualOriginalTransparentLambdaStepEquality := by
  intro n arity p hp v
  change evaluate (refined p.base.oldSource p.oldStep) v = evaluate p.oldStep v
  rw [refinedEvaluation]
  have h := repeatPreserves p.base.oldSource
    (fun state => evaluate p.oldStep (stateValues state))
    (transitionPreserves n arity p hp) (Nat.unpair (v.get 2)).1 (liveValue v)
  simpa only [stateValuesLive] using h

theorem actualOriginalTransparentLambdaStepCalibration : ActualOriginalTransparentLambdaStepCalibration := by
  intro n arity p hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
  intro v
  exact (actualOriginalTransparentLambdaStepEquality n arity p hp v).trans (hp.2.2.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeProof
