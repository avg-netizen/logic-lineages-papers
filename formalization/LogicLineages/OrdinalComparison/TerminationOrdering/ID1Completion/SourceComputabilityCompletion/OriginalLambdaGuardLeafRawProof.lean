module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafRawProof
open OriginalLambdaGuardLeaf
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (vectorOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem lambdaTestEvaluation (v : List.Vector Nat 1) :
    evaluate lambdaTest v = if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 then 1 else 0 := by
  rw [lambdaTest,sameEvaluation,OriginalLambdaConstructorEvaluationProof.tagEvaluation]
  rfl

theorem sourceLambdaEvaluation (v : List.Vector Nat 4) :
    evaluate sourceLambda v = if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 then 1 else 0 := by
  change evaluate lambdaTest (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  rw [lambdaTestEvaluation]
  rfl

theorem targetLambdaEvaluation (v : List.Vector Nat 4) :
    evaluate targetLambda v = if (Nat.unpair (Nat.unpair (v.get 1)).2).1 = 1 then 1 else 0 := by
  change evaluate lambdaTest (List.Vector.ofFn fun _ : Fin 1 => v.get 1) = _
  rw [lambdaTestEvaluation]
  rfl

theorem sourceDomainEvaluation (v : List.Vector Nat 4) :
    evaluate sourceDomain v = (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1 := by
  change evaluate OriginalLambdaConstructor.domain (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  rw [OriginalLambdaConstructorEvaluationProof.domainEvaluation]
  rfl

theorem sourceCodomainEvaluation (v : List.Vector Nat 4) :
    evaluate sourceCodomain v = (Nat.unpair ((Nat.unpair (v.get 0)).1 - 1)).2 := by
  change evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate (leftOf (.projection 0)) v) = _
  rw [vectorOne,InternalListCodecEvaluationProof.tailEvaluation,leftOfEvaluation]
  rfl

theorem sourceBodyEvaluation (v : List.Vector Nat 4) :
    evaluate sourceBody v = Nat.pair (Nat.unpair ((Nat.unpair (v.get 0)).1 - 1)).2
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2 := by
  change evaluate OriginalLambdaConstructor.bodyCode
    (List.Vector.ofFn fun i : Fin 2 => evaluate ((![sourceCodomain,Program.projection 0] : Fin 2 → Program 4) i) v) = _
  rw [OriginalLambdaConstructorEvaluationProof.bodyEvaluation]
  change Nat.pair (evaluate sourceCodomain v)
    (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2 = _
  rw [sourceCodomainEvaluation]

theorem targetBodyEvaluation (v : List.Vector Nat 4) :
    evaluate targetBody v = Nat.pair (Nat.unpair ((Nat.unpair (v.get 0)).1 - 1)).2
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).2 := by
  change evaluate OriginalLambdaConstructor.bodyCode
    (List.Vector.ofFn fun i : Fin 2 => evaluate ((![sourceCodomain,Program.projection 1] : Fin 2 → Program 4) i) v) = _
  rw [OriginalLambdaConstructorEvaluationProof.bodyEvaluation]
  change Nat.pair (evaluate sourceCodomain v)
    (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).2 = _
  rw [sourceCodomainEvaluation]

theorem stripCertificateEvaluation (v : List.Vector Nat 1) :
    evaluate stripCertificate v = OriginalLambdaCertificate.stripStep (v.get 0) := by
  unfold stripCertificate
  rw [pairOfEvaluation,rightEvaluation]
  change Nat.pair (evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate InternalUnpair.left v))
      (Nat.unpair (v.get 0)).2 = _
  rw [vectorOne,InternalListCodecEvaluationProof.tailEvaluation,leftEvaluation]
  rfl

theorem childCertificateEvaluation (v : List.Vector Nat 4) :
    evaluate childCertificate v = OriginalLambdaCertificate.stripStep (v.get 2) := by
  change evaluate stripCertificate (List.Vector.ofFn fun _ : Fin 1 => v.get 2) = _
  rw [stripCertificateEvaluation]
  rfl

theorem childParameterEvaluation (v : List.Vector Nat 4) :
    evaluate childParameter v = Nat.pair (Nat.unpair (v.get 3)).1
      (Nat.succ (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1
        (Nat.unpair (v.get 3)).2)) := by
  unfold childParameter
  rw [pairOfEvaluation,leftOfEvaluation,consOfEvaluation,sourceDomainEvaluation,rightOfEvaluation]
  simp only [evaluate,Nat.add_comm 1,Nat.succ_eq_add_one]

theorem actualOriginalLambdaGuardLeafRawCalibration :
    OriginalLambdaGuardLeafTargets.ActualOriginalLambdaGuardLeafRawCalibration := by
  constructor
  · intro certificate
    exact stripCertificateEvaluation (List.Vector.ofFn ![certificate])
  · intro v
    exact ⟨sourceDomainEvaluation v,sourceCodomainEvaluation v,sourceBodyEvaluation v,
      targetBodyEvaluation v,childCertificateEvaluation v,childParameterEvaluation v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafRawProof
