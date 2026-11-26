module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaControlProof
open OriginalHereditaryLambda OriginalHereditaryLambdaRawProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem zeroEvaluation {n : Nat} (v : List.Vector Nat n) :
    evaluate (InternalAcceptance.constantZero n) v = 0 := rfl

theorem oneEvaluation {n : Nat} (v : List.Vector Nat n) :
    evaluate (InternalLessThan.constantOne n) v = 1 := rfl

theorem nilPathEvaluation (v : List.Vector Nat 4) :
    evaluate (.composition InternalListCodec.nilTest (fun _ : Fin 1 => path)) v =
      if (Nat.unpair (v.get 2)).1 = 0 then 1 else 0 := by
  change evaluate InternalListCodec.nilTest (List.Vector.ofFn fun _ : Fin 1 => evaluate path v) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne,InternalListCodecEvaluationProof.nilEvaluation,
    pathEvaluation]

theorem pathNonemptyEvaluation (v : List.Vector Nat 4) :
    evaluate pathNonempty v = if (Nat.unpair (v.get 2)).1 = 0 then 0 else 1 := by
  rw [pathNonempty,evalBranch,evalNormalize,nilPathEvaluation,oneEvaluation,zeroEvaluation]
  by_cases h : (Nat.unpair (v.get 2)).1 = 0 <;> simp [h]

theorem pathHeadLambdaEvaluation (v : List.Vector Nat 4) :
    evaluate pathHeadLambda v =
      if (Nat.unpair ((Nat.unpair (v.get 2)).1 - 1)).1 = 0 then 1 else 0 := by
  rw [pathHeadLambda,sameEvaluation,zeroEvaluation]
  change (if evaluate InternalListCodec.headCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate path v) = 0 then 1 else 0) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne,InternalListCodecEvaluationProof.headEvaluation,
    pathEvaluation]

theorem lamPathEvaluation (v : List.Vector Nat 4) :
    evaluate lamPath v = lamPathValue v := by
  rw [lamPath,conjunctionEvaluation,pathNonemptyEvaluation,pathHeadLambdaEvaluation]
  by_cases hz : (Nat.unpair (v.get 2)).1 = 0 <;>
    by_cases hh : (Nat.unpair ((Nat.unpair (v.get 2)).1 - 1)).1 = 0 <;>
      simp [lamPathValue,hz,hh]

theorem stopEvaluation (v : List.Vector Nat 4) : evaluate stop v = stopValue v := by
  rw [stop,evalBranch,evalNormalize,OriginalLambdaGuardLeafRawProof.sourceLambdaEvaluation,
    oneEvaluation,evalNormalize,OriginalLambdaGuardLeafEvaluationSupportProof.sameBottomEvaluation]
  by_cases hl : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 <;>
    by_cases hb : v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1
      (Nat.pair 3 (Nat.unpair (v.get 0)).1) <;>
        simp [stopValue,hl,hb]

theorem matchingTargetEvaluation (v : List.Vector Nat 4) :
    evaluate OriginalLambdaGuardLeaf.matchingTarget v = matchingTargetValue v := by
  by_cases hl : (Nat.unpair (Nat.unpair (v.get 1)).2).1 = 1 <;>
    by_cases ht : (Nat.unpair (v.get 1)).1 = (Nat.unpair (v.get 0)).1 <;>
      by_cases hd : (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).1 =
        (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1 <;>
    simp [OriginalLambdaGuardLeaf.matchingTarget,conjunctionEvaluation,
      OriginalLambdaGuardLeafRawProof.targetLambdaEvaluation,sameEvaluation,leftOfEvaluation,
      projectionEvaluation,OriginalLambdaGuardLeafRawProof.sourceDomainEvaluation,
      OriginalLambdaGuardLeafEvaluationSupportProof.targetDomainEvaluation,
      matchingTargetValue,hl,ht,hd]

theorem advanceGuardEvaluation (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (advanceGuard oldStep) v =
      if matchingTargetValue v = 1 ∧ lamPathValue v = 1 ∧
        evaluate oldStep (childValues v) = 1 then 1 else 0 := by
  rw [advanceGuard,conjunctionEvaluation,conjunctionEvaluation,
    matchingTargetEvaluation,lamPathEvaluation,childCheckEvaluation]
  by_cases hm : matchingTargetValue v = 1 <;>
    by_cases hl : lamPathValue v = 1 <;>
      by_cases hc : evaluate oldStep (childValues v) = 1 <;> simp [hm,hl,hc]

theorem transitionEvaluation (oldStep : Program 4) (state : Nat) :
    evaluate (transition oldStep) (List.Vector.ofFn ![state]) = transitionValue oldStep state := by
  simp only [transition,evalBranch,evalNormalize,atStateEvaluation,stopEvaluation,
    advanceGuardEvaluation,childLiveEvaluation,zeroEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero]
  by_cases hz : state = 0 <;>
    by_cases hs : stopValue (stateValues state) = 1 <;>
      by_cases ha : matchingTargetValue (stateValues state) = 1 ∧
        lamPathValue (stateValues state) = 1 ∧
          evaluate oldStep (childValues (stateValues state)) = 1 <;>
    simp [transitionValue,hz,hs,ha]

theorem finishEvaluation (state : Nat) :
    evaluate finish (List.Vector.ofFn ![state]) = finishValue state := by
  rw [finish,evalBranch,atStateEvaluation,stopEvaluation]
  rfl

theorem stopValueBoolean (v : List.Vector Nat 4) : stopValue v = 0 ∨ stopValue v = 1 := by
  unfold stopValue
  split_ifs <;> simp

theorem transitionLiveStopped (oldStep : Program 4) (v : List.Vector Nat 4)
    (hs : stopValue v = 1) :
    evaluate (transition oldStep) (List.Vector.ofFn ![liveValue v]) = liveValue v := by
  rw [transitionEvaluation]
  simp [transitionValue,liveValueNonzero,stateValuesLive,hs]

theorem transitionLiveAdvance (oldStep : Program 4) (v : List.Vector Nat 4)
    (hs : stopValue v = 0) (hm : matchingTargetValue v = 1)
    (hl : lamPathValue v = 1) (hc : evaluate oldStep (childValues v) = 1) :
    evaluate (transition oldStep) (List.Vector.ofFn ![liveValue v]) = liveValue (childValues v) := by
  rw [transitionEvaluation]
  simp [transitionValue,liveValueNonzero,stateValuesLive,hs,hm,hl,hc]

theorem finishLive (v : List.Vector Nat 4) :
    evaluate finish (List.Vector.ofFn ![liveValue v]) = stopValue v := by
  rw [finishEvaluation]
  simp [finishValue,liveValueNonzero,stateValuesLive]

theorem actualOriginalHereditaryLambdaControlCalibration :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaControlCalibration := by
  refine ⟨?_,advanceGuardEvaluation,transitionEvaluation,finishEvaluation⟩
  intro v
  exact ⟨stopEvaluation v,lamPathEvaluation v,matchingTargetEvaluation v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaControlProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaControlProof
