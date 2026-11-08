module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalParameterizedApplicationResultStack InternalApplicationResultStack
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationResultStackEvaluationProof
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation unaryEvaluation exactOneEvaluation)

theorem liftPEvaluation (P : Program 1) (v : List.Vector Nat 2) :
    evaluate (liftP P) v = evaluate P (List.Vector.ofFn ![v.get 0]) := by
  change evaluate P (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  congr 1

theorem wirePEvaluation {n : Nat} (P : Program (n+1))
    (selectors : Fin n → Program 1) (v : List.Vector Nat 2) :
    evaluate (wireP P selectors) v = evaluate P (List.Vector.ofFn
      (appendParameter (fun i => evaluate (selectors i) (List.Vector.ofFn ![v.get 0])) (v.get 1))) := by
  change evaluate P (List.Vector.ofFn fun i =>
    evaluate (appendParameter (fun j => liftP (selectors j)) (.projection (1 : Fin 2)) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendParameter, projectionEvaluation]
  · simp [appendParameter, liftPEvaluation]

theorem wireOneEvaluation (P : Program 2) (selector : Program 1) (v : List.Vector Nat 2) :
    evaluate (wireP P ![selector]) v = evaluate P (List.Vector.ofFn
      ![evaluate selector (List.Vector.ofFn ![v.get 0]),v.get 1]) := by
  rw [wirePEvaluation]
  congr 1

theorem openGuardPEvaluation (guard : Program 2) (v : List.Vector Nat 2) :
    evaluate (openGuardP guard) v =
      if InternalApplicationValidityStack.tagValue (v.get 0) = 2 ∧ evaluate guard v = 1 then 1 else 0 := by
  simp only [openGuardP, conjunctionEvaluation, liftPEvaluation, sameEvaluation,
    constructorTagEvaluation, projectionEvaluation, twoEvaluation,
    List.Vector.get_ofFn, Matrix.cons_val_zero,
    InternalApplicationValidityStack.tagValue, InternalApplicationValidityStack.payloadValue]
  split_ifs <;> simp_all

theorem returnStateEvaluation (v : List.Vector Nat 3) :
    evaluate returnState v = Nat.pair 1 (Nat.pair (v.get 1) (1 + Nat.pair (v.get 0) (v.get 2))) := by
  simp only [returnState, liveOfEvaluation, consOfEvaluation, projectionEvaluation]

theorem leafReturnedPEvaluation (leaf : Program 2) (v : List.Vector Nat 2) :
    evaluate (leafReturnedP leaf) v = Nat.pair 1
      (Nat.pair (evaluate rest (List.Vector.ofFn ![v.get 0]))
        (1 + Nat.pair (evaluate leaf (List.Vector.ofFn
          ![evaluate currentValue (List.Vector.ofFn ![v.get 0]),v.get 1]))
          (evaluate results (List.Vector.ofFn ![v.get 0])))) := by
  change evaluate returnState (List.Vector.ofFn ![
    evaluate (wireP leaf ![currentValue]) v,
    evaluate (liftP rest) v, evaluate (liftP results) v]) = _
  simp only [returnStateEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    wireOneEvaluation, liftPEvaluation]

theorem combinedPEvaluation (combine : Program 5) (v : List.Vector Nat 2) :
    evaluate (combinedP combine) v = evaluate combine (List.Vector.ofFn
      ![(Nat.unpair (evaluate currentValue (List.Vector.ofFn ![v.get 0]))).1,
        (Nat.unpair (evaluate currentValue (List.Vector.ofFn ![v.get 0]))).2,
        (Nat.unpair ((Nat.unpair (evaluate results (List.Vector.ofFn ![v.get 0]) - 1)).2 - 1)).1,
        (Nat.unpair (evaluate results (List.Vector.ofFn ![v.get 0]) - 1)).1,v.get 1]) := by
  rw [combinedP, wirePEvaluation]
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change Fin.lastCases (v.get 1)
      (fun j => evaluate
        ((![leftOf currentValue, rightOf currentValue, headOf (tailOf results), headOf results] :
          Fin 4 → Program 1) j) (List.Vector.ofFn ![v.get 0]))
      (Fin.last 4) = v.get 1
    rw [Fin.lastCases_last]
  · simp only [List.Vector.get_ofFn, appendParameter, Fin.lastCases_castSucc]
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (fun k => Fin.elim0 k)))) j <;>
      simp [leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

theorem finishReturnedPEvaluation (combine : Program 5) (v : List.Vector Nat 2) :
    evaluate (finishReturnedP combine) v = Nat.pair 1
      (Nat.pair (evaluate rest (List.Vector.ofFn ![v.get 0]))
        (1 + Nat.pair (evaluate combine (List.Vector.ofFn
          ![(Nat.unpair (evaluate currentValue (List.Vector.ofFn ![v.get 0]))).1,
            (Nat.unpair (evaluate currentValue (List.Vector.ofFn ![v.get 0]))).2,
            (Nat.unpair ((Nat.unpair (evaluate results (List.Vector.ofFn ![v.get 0]) - 1)).2 - 1)).1,
            (Nat.unpair (evaluate results (List.Vector.ofFn ![v.get 0]) - 1)).1,v.get 1]))
          (Nat.unpair ((Nat.unpair (evaluate results (List.Vector.ofFn ![v.get 0]) - 1)).2 - 1)).2)) := by
  change evaluate returnState (List.Vector.ofFn ![
    evaluate (combinedP combine) v, evaluate (liftP rest) v,
    evaluate (liftP (tailOf (tailOf results))) v]) = _
  simp only [returnStateEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    combinedPEvaluation, liftPEvaluation,
    tailOfEvaluation]

theorem exactParameterizedApplicationResultStackTransitionEvaluation :
    InternalParameterizedApplicationResultStackTargets.ExactParameterizedApplicationResultStackTransitionEvaluation := by
  intro guard leaf combine state parameter
  simp only [transitionP, evalBranch, liftPEvaluation, exactOneEvaluation,
    sameEvaluation, zeroEvaluation, statusEvaluation, wireOneEvaluation,
    openGuardPEvaluation, leafReturnedPEvaluation, expandedEvaluation,
    finishReturnedPEvaluation, projectionEvaluation, tailOfEvaluation, frameTagEvaluation,
    currentValueEvaluation, currentFrameEvaluation, restEvaluation, workEvaluation, resultsEvaluation,
    List.Vector.get_ofFn, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold transitionValue
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEvaluationProof
