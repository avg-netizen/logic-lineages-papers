module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationValidityStack InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (vectorOne)

theorem oneEvaluation {n : Nat} (v : List.Vector Nat n) :
    evaluate (InternalLessThan.constantOne n) v = 1 := rfl

theorem zeroEvaluation {n : Nat} (v : List.Vector Nat n) :
    evaluate (InternalAcceptance.constantZero n) v = 0 := rfl

theorem unaryEvaluation (p q : Program 1) (v : List.Vector Nat 1) :
    evaluate (.composition p (fun _ : Fin 1 => q)) v =
      evaluate p (List.Vector.ofFn ![evaluate q v]) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate q v) = _
  congr 1

theorem statusEvaluation (v : List.Vector Nat 1) :
    evaluate status v = (Nat.unpair (v.get 0)).1 := leftEvaluation v

theorem workEvaluation (v : List.Vector Nat 1) :
    evaluate work v = (Nat.unpair (v.get 0)).2 := rightEvaluation v

theorem currentEvaluation (v : List.Vector Nat 1) :
    evaluate current v = (Nat.unpair ((Nat.unpair (v.get 0)).2 - 1)).1 := by
  change evaluate InternalListCodec.headCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate work v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.headEvaluation, workEvaluation]

theorem restEvaluation (v : List.Vector Nat 1) :
    evaluate rest v = (Nat.unpair ((Nat.unpair (v.get 0)).2 - 1)).2 := by
  change evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate work v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.tailEvaluation, workEvaluation]

theorem currentTypeEvaluation (v : List.Vector Nat 1) :
    evaluate currentType v = resultTypeValue (evaluate current v) := by
  rw [currentType, leftOfEvaluation]
  rfl

theorem currentTagEvaluation (v : List.Vector Nat 1) :
    evaluate currentTag v = tagValue (evaluate current v) := by
  rw [currentTag, constructorTagEvaluation]
  rfl

theorem currentDomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentDomain v = domainValue (evaluate current v) := by
  rw [currentDomain, appDomainEvaluation, appBodyEvaluation]
  rfl

theorem currentFunctionEvaluation (v : List.Vector Nat 1) :
    evaluate currentFunction v = functionChildValue (evaluate current v) := by
  rw [currentFunction, pairOfEvaluation, consOfEvaluation, currentDomainEvaluation,
    currentTypeEvaluation, functionPayloadEvaluation, appBodyEvaluation]
  rfl

theorem currentArgumentEvaluation (v : List.Vector Nat 1) :
    evaluate currentArgument v = argumentChildValue (evaluate current v) := by
  rw [currentArgument, pairOfEvaluation, currentDomainEvaluation,
    argumentPayloadEvaluation, appBodyEvaluation]
  rfl

theorem exactOneEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (exactOne p) v = if evaluate p v = 1 then 1 else 0 := by
  rw [exactOne, sameEvaluation, oneEvaluation]

theorem poppedEvaluation (v : List.Vector Nat 1) :
    evaluate popped v = Nat.pair 1 (evaluate rest v) := by
  rw [popped, pairOfEvaluation, oneEvaluation]

theorem expandedEvaluation (v : List.Vector Nat 1) :
    evaluate expanded v = Nat.pair 1
      (1 + Nat.pair (functionChildValue (evaluate current v))
        (1 + Nat.pair (argumentChildValue (evaluate current v)) (evaluate rest v))) := by
  rw [expanded, pairOfEvaluation, oneEvaluation, consOfEvaluation, consOfEvaluation,
    currentFunctionEvaluation, currentArgumentEvaluation]

theorem actualOriginalStackTransitionCalibration :
    InternalApplicationValidityStackTargets.ActualOriginalStackTransitionCalibration := by
  intro node leaf value
  simp only [transition, evalBranch, exactOneEvaluation, sameEvaluation, twoEvaluation,
    statusEvaluation, workEvaluation, currentTagEvaluation, unaryEvaluation,
    currentTypeEvaluation, poppedEvaluation, expandedEvaluation, currentEvaluation,
    restEvaluation, zeroEvaluation, projectionEvaluation, List.Vector.get_ofFn,
    Matrix.cons_val_zero]
  unfold transitionValue
  split_ifs <;> simp_all

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
