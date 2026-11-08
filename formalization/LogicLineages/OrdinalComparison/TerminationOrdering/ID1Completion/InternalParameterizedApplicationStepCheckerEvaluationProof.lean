module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationProof
open Source NumberedNumericDecoding NumberedNumericCarrier NumberedNumericStep
open NumberedAuxiliaryCoding ApplicationCertificateLift
open InternalApplicationStepPeel InternalParameterizedApplicationStepChecker
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationProof InternalApplicationStepPeelEvaluationSelectorSupportProof
open InternalApplicationStepCheckerEvaluationProof
  (stateTest endpointIdentity sourceReconstruction targetReconstruction certificateReconstruction)
open InternalParameterizedApplicationStepCheckerEvaluationSupportProof
open InternalParameterizedApplicationResultStackEvaluationProof (liftPEvaluation)
open InternalParameterizedApplicationResultStack (liftP)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

 theorem transitionPreserves (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 6) (parameter : Nat)
    (calibrated : EndpointCalibratedAt n arity symbols S Gamma endpoint parameter)
    (state : Nat) :
    stateTest n arity symbols S Gamma table
      (evaluate (transitionP endpoint) (List.Vector.ofFn ![state,parameter])) =
    stateTest n arity symbols S Gamma table state := by
  rw [(transitionCalibration n arity symbols S Gamma endpoint parameter calibrated state).2]
  unfold transitionValue
  split
  next h =>
    have hg : shape (view state) = true ∧
        endpointValue n arity symbols S Gamma (endpointInputs (view state)) = 1 := by
      simpa [guardValue] using h
    have hi := endpointIdentity n arity symbols S Gamma table (endpointInputs (view state))
      (Nat.pair (view state).pathTail (view state).payload) hg.2
    change numericStepTest n arity symbols S Gamma table
      (rawApplication (view state).domain (view state).sourceType
        ((endpointInputs (view state)).get 2) ((endpointInputs (view state)).get 4))
      (rawApplication (view state).domain (view state).sourceType
        ((endpointInputs (view state)).get 3) ((endpointInputs (view state)).get 4))
      (liftStep (Nat.pair (view state).pathTail (view state).payload)) = _ at hi
    rw [sourceReconstruction state hg.1,targetReconstruction state hg.1,
      certificateReconstruction state hg.1] at hi
    simpa only [stateTest,peeledValue,view,Nat.unpair_pair] using hi.symm
  next => rfl

theorem repeatPreserves (T : Program 2) (f : Nat → Bool) (parameter : Nat)
    (hp : ∀ s, f (evaluate T (List.Vector.ofFn ![s,parameter])) = f s)
    (code state : Nat) :
    f (evaluate (repeatP T)
      (code ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) = f state := by
  rw [repeatP,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation]
  change f (((NumberedMultisetNumeric.decodeNumbers code).getD []).foldr
    (fun _ result => evaluate T (List.Vector.ofFn ![result,parameter])) state) = f state
  generalize (NumberedMultisetNumeric.decodeNumbers code).getD [] = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldr_cons,hp] using ih

theorem normalizerPreserves (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 6) (parameter : Nat)
    (calibrated : EndpointCalibratedAt n arity symbols S Gamma endpoint parameter)
    (state : Nat) :
    stateTest n arity symbols S Gamma table
      (evaluate (normalizerP endpoint) (List.Vector.ofFn ![state,parameter])) =
    stateTest n arity symbols S Gamma table state := by
  change stateTest n arity symbols S Gamma table
    (evaluate (repeatP (transitionP endpoint))
      (List.Vector.ofFn fun i : Fin 3 => evaluate
        ((![liftP rawPath,.projection 0,.projection 1] : Fin 3 → Program 2) i)
          (List.Vector.ofFn ![state,parameter]))) = _
  rw [InternalEqualityTestEvaluationProof.vectorThree]
  exact repeatPreserves _ _ parameter
    (transitionPreserves n arity symbols S Gamma table endpoint parameter calibrated) _ state

theorem selectedCheckerEvaluation (oldChecker : Program 4) (state parameter : Nat) :
    evaluate (selectedCheckerP oldChecker) (List.Vector.ofFn ![state,parameter]) =
      evaluate oldChecker (List.Vector.ofFn
        ![evaluate source (List.Vector.ofFn ![state]),
          evaluate target (List.Vector.ofFn ![state]),
          evaluate step (List.Vector.ofFn ![state]),parameter]) := by
  rw [selectedCheckerP,wireThreeEvaluation]
  rfl

theorem actualParameterizedOriginalCheckerCalibration :
    InternalParameterizedApplicationStepCheckerTargets.ActualParameterizedOriginalCheckerCalibration := by
  intro n arity symbols S Gamma table endpoint oldChecker parameter he ho v
  let state := evaluate edgeCode (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2])
  let normalized := evaluate (normalizerP endpoint) (List.Vector.ofFn ![state,parameter])
  change evaluate (selectedCheckerP oldChecker)
    (List.Vector.ofFn ![normalized,parameter]) = _
  rw [selectedCheckerEvaluation]
  have hc := ho (List.Vector.ofFn
    ![evaluate source (List.Vector.ofFn ![normalized]),
      evaluate target (List.Vector.ofFn ![normalized]),
      evaluate step (List.Vector.ofFn ![normalized])])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hc
  rw [hc]
  rw [sourceViewEvaluation,targetViewEvaluation,stepViewEvaluation]
  change (stateTest n arity symbols S Gamma table normalized).toNat = _
  rw [normalizerPreserves n arity symbols S Gamma table endpoint parameter he state]
  dsimp [state]
  rw [edgeCodeEvaluation]
  simp only [stateTest,NumberedNumericQuotientEdge.edgeCertificateNumber,view,Nat.unpair_pair,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationProof
