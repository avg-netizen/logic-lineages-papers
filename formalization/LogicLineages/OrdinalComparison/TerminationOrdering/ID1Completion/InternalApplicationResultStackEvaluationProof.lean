module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationResultStack InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (vectorOne)
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation unaryEvaluation exactOneEvaluation)

theorem headOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (headOf p) v = (Nat.unpair (evaluate p v - 1)).1 := by
  change evaluate InternalListCodec.headCode (List.Vector.ofFn fun _ : Fin 1 => evaluate p v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.headEvaluation]

theorem tailOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (tailOf p) v = (Nat.unpair (evaluate p v - 1)).2 := by
  change evaluate InternalListCodec.tailCode (List.Vector.ofFn fun _ : Fin 1 => evaluate p v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.tailEvaluation]

theorem visitOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (visitOf p) v = visitValue (evaluate p v) := by
  rw [visitOf, pairOfEvaluation, zeroEvaluation]
  rfl

theorem finishOfEvaluation {n : Nat} (d e : Program n) (v : List.Vector Nat n) :
    evaluate (finishOf d e) v = finishValue (evaluate d v) (evaluate e v) := by
  rw [finishOf, pairOfEvaluation, pairOfEvaluation, oneEvaluation]
  rfl

theorem liveOfEvaluation {n : Nat} (work results : Program n) (v : List.Vector Nat n) :
    evaluate (liveOf work results) v = Nat.pair 1 (Nat.pair (evaluate work v) (evaluate results v)) := by
  rw [liveOf, pairOfEvaluation, pairOfEvaluation, oneEvaluation]

theorem statusEvaluation (v : List.Vector Nat 1) :
    evaluate status v = (Nat.unpair (v.get 0)).1 := leftEvaluation v

theorem workEvaluation (v : List.Vector Nat 1) :
    evaluate work v = (Nat.unpair (Nat.unpair (v.get 0)).2).1 := by
  rw [work, leftOfEvaluation, rightEvaluation]

theorem resultsEvaluation (v : List.Vector Nat 1) :
    evaluate results v = (Nat.unpair (Nat.unpair (v.get 0)).2).2 := by
  rw [results, rightOfEvaluation, rightEvaluation]

theorem currentFrameEvaluation (v : List.Vector Nat 1) :
    evaluate currentFrame v = (Nat.unpair (evaluate work v - 1)).1 := by
  rw [currentFrame, headOfEvaluation]

theorem restEvaluation (v : List.Vector Nat 1) :
    evaluate rest v = (Nat.unpair (evaluate work v - 1)).2 := by
  rw [rest, tailOfEvaluation]

theorem frameTagEvaluation (v : List.Vector Nat 1) :
    evaluate frameTag v = (Nat.unpair (evaluate currentFrame v)).1 := by
  rw [frameTag, leftOfEvaluation]

theorem currentValueEvaluation (v : List.Vector Nat 1) :
    evaluate currentValue v = (Nat.unpair (evaluate currentFrame v)).2 := by
  rw [currentValue, rightOfEvaluation]

theorem currentTypeEvaluation (v : List.Vector Nat 1) :
    evaluate currentType v = InternalApplicationValidityStack.resultTypeValue (evaluate currentValue v) := by
  rw [currentType, leftOfEvaluation]
  rfl

theorem currentDomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentDomain v = InternalApplicationValidityStack.domainValue (evaluate currentValue v) := by
  rw [currentDomain, appDomainEvaluation, appBodyEvaluation]
  rfl

theorem currentFunctionEvaluation (v : List.Vector Nat 1) :
    evaluate currentFunction v = InternalApplicationValidityStack.functionChildValue (evaluate currentValue v) := by
  rw [currentFunction, pairOfEvaluation, consOfEvaluation, currentDomainEvaluation,
    currentTypeEvaluation, functionPayloadEvaluation, appBodyEvaluation]
  rfl

theorem currentArgumentEvaluation (v : List.Vector Nat 1) :
    evaluate currentArgument v = InternalApplicationValidityStack.argumentChildValue (evaluate currentValue v) := by
  rw [currentArgument, pairOfEvaluation, currentDomainEvaluation, argumentPayloadEvaluation, appBodyEvaluation]
  rfl

theorem openGuardEvaluation (guard : Program 1) (v : List.Vector Nat 1) :
    evaluate (openGuard guard) v =
      if InternalApplicationValidityStack.tagValue (v.get 0) = 2 ∧ evaluate guard v = 1 then 1 else 0 := by
  simp only [openGuard, conjunctionEvaluation, sameEvaluation, constructorTagEvaluation,
    projectionEvaluation, twoEvaluation, InternalApplicationValidityStack.tagValue,
    InternalApplicationValidityStack.payloadValue]
  split_ifs <;> simp_all

theorem expandedEvaluation (v : List.Vector Nat 1) :
    evaluate expanded v = Nat.pair 1 (Nat.pair
      (1 + Nat.pair (visitValue (InternalApplicationValidityStack.functionChildValue (evaluate currentValue v)))
        (1 + Nat.pair (visitValue (InternalApplicationValidityStack.argumentChildValue (evaluate currentValue v)))
          (1 + Nat.pair (finishValue (InternalApplicationValidityStack.domainValue (evaluate currentValue v))
            (InternalApplicationValidityStack.resultTypeValue (evaluate currentValue v))) (evaluate rest v))))
      (evaluate results v)) := by
  simp only [expanded, liveOfEvaluation, consOfEvaluation, visitOfEvaluation, finishOfEvaluation,
    currentFunctionEvaluation, currentArgumentEvaluation, currentDomainEvaluation, currentTypeEvaluation]

theorem leafReturnedEvaluation (leaf : Program 1) (v : List.Vector Nat 1) :
    evaluate (leafReturned leaf) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (evaluate leaf (List.Vector.ofFn ![evaluate currentValue v])) (evaluate results v))) := by
  rw [leafReturned, liveOfEvaluation, consOfEvaluation, unaryEvaluation]

theorem combinedEvaluation (combine : Program 4) (v : List.Vector Nat 1) :
    evaluate (combined combine) v = evaluate combine (List.Vector.ofFn
      ![(Nat.unpair (evaluate currentValue v)).1,(Nat.unpair (evaluate currentValue v)).2,
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).1,
        (Nat.unpair (evaluate results v - 1)).1]) := by
  change evaluate combine (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((![leftOf currentValue,rightOf currentValue,headOf (tailOf results),headOf results] :
      Fin 4 → Program 1) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i <;>
    simp [leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

theorem finishReturnedEvaluation (combine : Program 4) (v : List.Vector Nat 1) :
    evaluate (finishReturned combine) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (evaluate combine (List.Vector.ofFn
        ![(Nat.unpair (evaluate currentValue v)).1,(Nat.unpair (evaluate currentValue v)).2,
          (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).1,
          (Nat.unpair (evaluate results v - 1)).1]))
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).2)) := by
  rw [finishReturned, liveOfEvaluation, consOfEvaluation, combinedEvaluation,
    tailOfEvaluation, tailOfEvaluation]

theorem actualOriginalResultStackTransitionCalibration :
    InternalApplicationResultStackTargets.ActualOriginalResultStackTransitionCalibration := by
  intro guard leaf combine value
  simp only [transition, evalBranch, exactOneEvaluation, sameEvaluation, zeroEvaluation,
    statusEvaluation, unaryEvaluation, openGuardEvaluation, leafReturnedEvaluation, expandedEvaluation,
    finishReturnedEvaluation, projectionEvaluation, tailOfEvaluation, frameTagEvaluation,
    currentValueEvaluation, currentFrameEvaluation, restEvaluation, workEvaluation, resultsEvaluation,
    List.Vector.get_ofFn, Matrix.cons_val_zero]
  unfold transitionValue
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
