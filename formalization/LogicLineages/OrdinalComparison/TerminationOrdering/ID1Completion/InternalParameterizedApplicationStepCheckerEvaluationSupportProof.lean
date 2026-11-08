module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalParameterizedApplicationStepChecker
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalParameterizedApplicationResultStack (wireP liftP appendParameter)
open InternalParameterizedApplicationResultStackEvaluationProof (liftPEvaluation wirePEvaluation)
open InternalApplicationStepPeelEvaluationProof InternalApplicationStepPeelEvaluationSelectorSupportProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationStepPeelEvaluationViewSupportProof InternalApplicationStepPeelEvaluationFieldSupportProof

theorem wireThreeEvaluation (P : Program 4) (selectors : Fin 3 → Program 1)
    (v : List.Vector Nat 2) :
    evaluate (wireP P selectors) v = evaluate P (List.Vector.ofFn
      ![evaluate (selectors 0) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 1) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 2) (List.Vector.ofFn ![v.get 0]),v.get 1]) := by
  rw [wirePEvaluation]
  congr 1

theorem wireFiveEvaluation (P : Program 6) (selectors : Fin 5 → Program 1)
    (v : List.Vector Nat 2) :
    evaluate (wireP P selectors) v = evaluate P (List.Vector.ofFn
      ![evaluate (selectors 0) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 1) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 2) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 3) (List.Vector.ofFn ![v.get 0]),
        evaluate (selectors 4) (List.Vector.ofFn ![v.get 0]),v.get 1]) := by
  rw [wirePEvaluation]
  congr 1

theorem endpointTypeGuardPEvaluation (v : List.Vector Nat 5) (parameter : Nat) :
    evaluate endpointTypeGuardP
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,parameter]) =
      evaluate endpointTypeGuard v := by
  change evaluate endpointTypeGuard (List.Vector.ofFn fun i : Fin 5 =>
    evaluate ((![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4] :
      Fin 5 → Program 6) i)
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,parameter])) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (fun k => Fin.elim0 k))))) i <;> rfl

theorem endpointAtPEvaluation (endpoint : Program 6) (state parameter : Nat) :
    evaluate (endpointAtP endpoint) (List.Vector.ofFn ![state,parameter]) =
      if evaluate endpoint (List.Vector.ofFn
        ![(endpointInputs (view state)).get 0,(endpointInputs (view state)).get 1,
          (endpointInputs (view state)).get 2,(endpointInputs (view state)).get 3,
          (endpointInputs (view state)).get 4,parameter]) = 1 then 1 else 0 := by
  rw [endpointAtP,wireFiveEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  rw [domainViewEvaluation,codomainViewEvaluation,functionCodeViewEvaluation,
    targetFunctionCodeViewEvaluation,argumentCodeViewEvaluation]
  change evaluate (endpointGuardP endpoint) (List.Vector.ofFn
    ![(endpointInputs (view state)).get 0,(endpointInputs (view state)).get 1,
      (endpointInputs (view state)).get 2,(endpointInputs (view state)).get 3,
      (endpointInputs (view state)).get 4,parameter]) = _
  rw [endpointGuardP,conjunctionEvaluation,endpointTypeGuardPEvaluation,endpointTypeGuardEvaluation]
  simp

theorem transitionCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Source.Ty) (endpoint : Program 6) (parameter : Nat)
    (calibrated : EndpointCalibratedAt n arity symbols S Gamma endpoint parameter)
    (state : Nat) :
    evaluate (guardP endpoint) (List.Vector.ofFn ![state,parameter]) =
      guardValue n arity symbols S Gamma state ∧
    evaluate (transitionP endpoint) (List.Vector.ofFn ![state,parameter]) =
      transitionValue n arity symbols S Gamma state := by
  have hg : evaluate (guardP endpoint) (List.Vector.ofFn ![state,parameter]) =
      guardValue n arity symbols S Gamma state := by
    rw [guardP,conjunctionEvaluation,liftPEvaluation]
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
    rw [structuralGuardEvaluation,endpointAtPEvaluation,calibrated]
    simp [guardValue]
  refine ⟨hg, ?_⟩
  rw [transitionP,evalBranch,hg,liftPEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
  rw [peeledStateEvaluation,projectionEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
  unfold transitionValue guardValue
  split <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationSupportProof
