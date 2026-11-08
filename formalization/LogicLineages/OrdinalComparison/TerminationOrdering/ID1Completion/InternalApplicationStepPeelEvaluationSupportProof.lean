module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

 theorem projectionEvaluation {n : Nat} (i : Fin n) (v : List.Vector Nat n) :
    evaluate (.projection i) v = v.get i := rfl

 theorem conjunctionEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (InternalAcceptance.conjunction p q) v =
      if evaluate p v = 1 ∧ evaluate q v = 1 then 1 else 0 :=
  actualConjunctionEvaluation n p q v

 theorem sameEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (same p q) v = if evaluate p v = evaluate q v then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i : Fin 2 => evaluate (![p,q] i) v) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation _ _

 theorem pathHeadEvaluation (v : List.Vector Nat 1) :
    evaluate pathHead v = (Nat.unpair (evaluate rawPath v - 1)).1 := by
  change evaluate InternalListCodec.headCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate rawPath v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.headEvaluation]

 theorem pathTailEvaluation (v : List.Vector Nat 1) :
    evaluate pathTail v = (Nat.unpair (evaluate rawPath v - 1)).2 := by
  change evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate rawPath v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.tailEvaluation]

 theorem nonemptyPathEvaluation (v : List.Vector Nat 1) :
    evaluate nonemptyPath v = if evaluate rawPath v = 0 then 0 else 1 := by
  rw [nonemptyPath, evalBranch]
  rfl

 theorem sourceEvaluation (v : List.Vector Nat 1) :
    evaluate source v = (Nat.unpair (v.get 0)).1 := by
  rw [source,leftEvaluation]

 theorem targetEvaluation (v : List.Vector Nat 1) :
    evaluate target v = (Nat.unpair (Nat.unpair (v.get 0)).2).1 := by
  rw [target,leftOfEvaluation,rightEvaluation]

 theorem stepEvaluation (v : List.Vector Nat 1) :
    evaluate step v = (Nat.unpair (Nat.unpair (v.get 0)).2).2 := by
  rw [step,rightOfEvaluation,rightEvaluation]

 theorem rawPathEvaluation (v : List.Vector Nat 1) :
    evaluate rawPath v = (Nat.unpair (evaluate step v)).1 := by
  rw [rawPath,leftOfEvaluation]

 theorem outerTypeEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (outerType p) v = (Nat.unpair (evaluate p v)).1 := by
  rw [outerType,leftOfEvaluation]

 theorem constructorTagEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (constructorTag p) v = (Nat.unpair (Nat.unpair (evaluate p v)).2).1 := by
  rw [constructorTag,leftOfEvaluation,rightOfEvaluation]

 theorem appBodyEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (appBody p) v = (Nat.unpair (Nat.unpair (evaluate p v)).2).2 := by
  rw [appBody,rightOfEvaluation,rightOfEvaluation]

 theorem appDomainEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (appDomain p) v = (Nat.unpair (evaluate (appBody p) v)).1 := by
  rw [appDomain,leftOfEvaluation]

 theorem functionPayloadEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (functionPayload p) v = (Nat.unpair (Nat.unpair (evaluate (appBody p) v)).2).1 := by
  rw [functionPayload,leftOfEvaluation,rightOfEvaluation]

 theorem argumentPayloadEvaluation (p : Program 1) (v : List.Vector Nat 1) :
    evaluate (argumentPayload p) v = (Nat.unpair (Nat.unpair (evaluate (appBody p) v)).2).2 := by
  rw [argumentPayload,rightOfEvaluation,rightOfEvaluation]

 theorem domainEvaluation (v : List.Vector Nat 1) :
    evaluate domain v = evaluate (appDomain source) v := rfl

 theorem codomainEvaluation (v : List.Vector Nat 1) :
    evaluate codomain v = evaluate (outerType source) v := rfl

 theorem arrowTypeEvaluation (v : List.Vector Nat 1) :
    evaluate arrowType v = 1 + Nat.pair (evaluate domain v) (evaluate codomain v) := by
  rw [arrowType,consOfEvaluation]

 theorem functionCodeEvaluation (v : List.Vector Nat 1) :
    evaluate functionCode v = Nat.pair (evaluate arrowType v) (evaluate (functionPayload source) v) := by
  rw [functionCode,pairOfEvaluation]

 theorem targetFunctionCodeEvaluation (v : List.Vector Nat 1) :
    evaluate targetFunctionCode v = Nat.pair (evaluate arrowType v) (evaluate (functionPayload target) v) := by
  rw [targetFunctionCode,pairOfEvaluation]

 theorem argumentCodeEvaluation (v : List.Vector Nat 1) :
    evaluate argumentCode v = Nat.pair (evaluate domain v) (evaluate (argumentPayload source) v) := by
  rw [argumentCode,pairOfEvaluation]

 theorem peeledStepEvaluation (v : List.Vector Nat 1) :
    evaluate peeledStep v = Nat.pair (evaluate pathTail v) (Nat.unpair (evaluate step v)).2 := by
  rw [peeledStep,pairOfEvaluation,rightOfEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
