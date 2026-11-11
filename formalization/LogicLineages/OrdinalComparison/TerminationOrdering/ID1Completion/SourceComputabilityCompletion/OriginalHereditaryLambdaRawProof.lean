module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRawProof
open OriginalHereditaryLambda
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem prefixCertificateEvaluation (v : List.Vector Nat 1) :
    evaluate prefixCertificate v = OriginalLambdaCertificate.liftStep (v.get 0) := by
  unfold prefixCertificate
  rw [pairOfEvaluation,consOfEvaluation,leftEvaluation,rightEvaluation]
  rfl

theorem pathEvaluation (v : List.Vector Nat 4) :
    evaluate path v = (Nat.unpair (v.get 2)).1 := by
  rw [path,leftOfEvaluation]
  rfl

theorem liveEvaluation (v : List.Vector Nat 4) : evaluate live v = liveValue v := by
  change Nat.succ (evaluate
    (pairOf (Program.projection 0)
      (pairOf (.projection 1) (pairOf (.projection 2) (.projection 3)))) v) = _
  rw [pairOfEvaluation,pairOfEvaluation,pairOfEvaluation]
  rfl

theorem sourceBodyEvaluation (v : List.Vector Nat 4) :
    evaluate OriginalLambdaGuardLeaf.sourceBody v = (childValues v).get 0 := by
  rw [OriginalLambdaGuardLeafRawProof.sourceBodyEvaluation]
  rfl

theorem targetBodyEvaluation (v : List.Vector Nat 4) :
    evaluate OriginalLambdaGuardLeaf.targetBody v = (childValues v).get 1 := by
  rw [OriginalLambdaGuardLeafRawProof.targetBodyEvaluation]
  rfl

theorem childCertificateEvaluation (v : List.Vector Nat 4) :
    evaluate OriginalLambdaGuardLeaf.childCertificate v = (childValues v).get 2 := by
  rw [OriginalLambdaGuardLeafRawProof.childCertificateEvaluation]
  rfl

theorem childParameterEvaluation (v : List.Vector Nat 4) :
    evaluate OriginalLambdaGuardLeaf.childParameter v = (childValues v).get 3 := by
  rw [OriginalLambdaGuardLeafRawProof.childParameterEvaluation]
  rfl

theorem childVectorEvaluation (v : List.Vector Nat 4) :
    List.Vector.ofFn (fun i : Fin 4 => evaluate
      ((![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
        OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] :
        Fin 4 → Program 4) i) v) = childValues v := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))) i
  · exact sourceBodyEvaluation v
  · exact targetBodyEvaluation v
  · exact childCertificateEvaluation v
  · exact childParameterEvaluation v

theorem childLiveEvaluation (v : List.Vector Nat 4) :
    evaluate childLive v = liveValue (childValues v) := by
  change evaluate live (List.Vector.ofFn (fun i : Fin 4 => evaluate
    ((![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
      OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] :
      Fin 4 → Program 4) i) v)) = _
  rw [childVectorEvaluation,liveEvaluation]

theorem childCheckEvaluation (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (OriginalLambdaGuardLeaf.childCheck oldStep) v =
      evaluate oldStep (childValues v) := by
  change evaluate oldStep (List.Vector.ofFn (fun i : Fin 4 => evaluate
    ((![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
      OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] :
      Fin 4 → Program 4) i) v)) = _
  rw [childVectorEvaluation]

theorem statePayloadEvaluation (v : List.Vector Nat 1) :
    evaluate statePayload v = v.get 0 - 1 := by
  unfold statePayload
  rw [oneVector v,InternalEqualityTestEvaluationProof.exactPredecessorEvaluation]
  exact Nat.pred_eq_sub_one

theorem stateSourceEvaluation (state : Nat) :
    evaluate stateSource (List.Vector.ofFn ![state]) = (stateValues state).get 0 := by
  rw [stateSource,leftOfEvaluation,statePayloadEvaluation]
  rfl

theorem stateTargetEvaluation (state : Nat) :
    evaluate stateTarget (List.Vector.ofFn ![state]) = (stateValues state).get 1 := by
  rw [stateTarget,leftOfEvaluation,rightOfEvaluation,statePayloadEvaluation]
  rfl

theorem stateCertificateEvaluation (state : Nat) :
    evaluate stateCertificate (List.Vector.ofFn ![state]) = (stateValues state).get 2 := by
  rw [stateCertificate,leftOfEvaluation,rightOfEvaluation,rightOfEvaluation,statePayloadEvaluation]
  rfl

theorem stateParameterEvaluation (state : Nat) :
    evaluate stateParameter (List.Vector.ofFn ![state]) = (stateValues state).get 3 := by
  rw [stateParameter,rightOfEvaluation,rightOfEvaluation,rightOfEvaluation,statePayloadEvaluation]
  rfl

theorem stateVectorEvaluation (state : Nat) :
    List.Vector.ofFn (fun i : Fin 4 => evaluate
      ((![stateSource,stateTarget,stateCertificate,stateParameter] : Fin 4 → Program 1) i)
      (List.Vector.ofFn ![state])) = stateValues state := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))) i
  · exact stateSourceEvaluation state
  · exact stateTargetEvaluation state
  · exact stateCertificateEvaluation state
  · exact stateParameterEvaluation state

theorem atStateEvaluation (p : Program 4) (state : Nat) :
    evaluate (atState p) (List.Vector.ofFn ![state]) = evaluate p (stateValues state) := by
  change evaluate p (List.Vector.ofFn (fun i : Fin 4 => evaluate
    ((![stateSource,stateTarget,stateCertificate,stateParameter] : Fin 4 → Program 1) i)
    (List.Vector.ofFn ![state]))) = _
  rw [stateVectorEvaluation]

theorem stateValuesLive (v : List.Vector Nat 4) : stateValues (liveValue v) = v := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))) i <;>
    simp [stateValues,liveValue,Nat.unpair_pair]

theorem liveValueNonzero (v : List.Vector Nat 4) : liveValue v ≠ 0 :=
  Nat.succ_ne_zero _

theorem actualOriginalHereditaryLambdaRawCalibration :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaRawCalibration := by
  refine ⟨?_,?_,?_,atStateEvaluation⟩
  · intro certificate
    exact prefixCertificateEvaluation (List.Vector.ofFn ![certificate])
  · intro v
    exact ⟨pathEvaluation v,liveEvaluation v,sourceBodyEvaluation v,targetBodyEvaluation v,
      childCertificateEvaluation v,childParameterEvaluation v,childLiveEvaluation v⟩
  · intro state
    exact ⟨stateSourceEvaluation state,stateTargetEvaluation state,
      stateCertificateEvaluation state,stateParameterEvaluation state⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRawProof
