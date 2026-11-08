module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
open InternalApplicationResultStack InternalParameterizedApplicationResultStack
open InternalApplicationResultFoldCalibration InternalParameterizedApplicationResultFoldCalibration
open InternalParameterizedApplicationResultStackEvaluationProof
open InternalParameterizedNumericIterationEvaluationProof
open InternalApplicationResultStackStateProof
open InternalApplicationResultFoldCalibrationEvaluationProof
open InternalApplicationResultFoldCalibrationCompletionProof
open InternalApplicationCertifiedResultFoldClosureCalibrationProof
open InternalEqualityTestEvaluationProof (vectorTwo vectorThree)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem actualOriginalParameterizedSemanticResultFoldEquation :
    InternalParameterizedApplicationResultFoldCalibrationTargets.ActualOriginalParameterizedSemanticResultFoldEquation := by
  intro guard leaf combine value parameter
  simpa only [semanticFoldP] using
    InternalApplicationResultFoldCalibrationMeaningProof.actualOriginalSemanticResultFoldEquation
      (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
      (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
      (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter])) value

theorem iterateEncoded (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (count : Nat) (state : State) :
    Nat.iterate (transitionValue guard leaf combine) count (encodeState state) =
      encodeState (stateIterate guard leaf combine count state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply', ih, actualOriginalEncodedResultStackTransition]
    rfl

theorem actualOriginalParameterizedEncodedResultStackIteration :
    InternalParameterizedApplicationResultFoldCalibrationTargets.ActualOriginalParameterizedEncodedResultStackIteration := by
  intro guard leaf combine count state parameter
  change evaluate (InternalParameterizedNumericIteration.repeatP (transitionP guard leaf combine))
    (List.Vector.ofFn ![count, encodeState state, parameter]) = _
  rw [vectorThree]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [exactParameterizedNumericIterationEvaluation]
  have ht : (fun x => evaluate (transitionP guard leaf combine)
      (x ::ᵥ parameter ::ᵥ List.Vector.nil)) =
      transitionValue
        (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
        (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
        (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter])) := by
    funext x
    simpa only [vectorTwo, Matrix.cons_val_zero, Matrix.cons_val_one] using
      exactParameterizedApplicationResultStackTransitionEvaluation guard leaf combine x parameter
  rw [ht, iterateEncoded]

theorem runPEvaluation (guard leaf : Program 2) (combine : Program 5)
    (value parameter : Nat) :
    evaluate (runP guard leaf combine) (List.Vector.ofFn ![value,parameter]) =
      encodeState (stateIterate
        (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
        (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
        (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter]))
        (fuelValue value) (⟨1, [visitValue value], []⟩ : State)) := by
  change evaluate (iterateP guard leaf combine)
    (List.Vector.ofFn fun i : Fin 3 =>
      evaluate ((![liftP fuel, liftP initial, .projection 1] : Fin 3 → Program 2) i)
        (List.Vector.ofFn ![value,parameter])) = _
  have hv : (List.Vector.ofFn fun i : Fin 3 =>
      evaluate ((![liftP fuel, liftP initial, .projection 1] : Fin 3 → Program 2) i)
        (List.Vector.ofFn ![value,parameter])) =
      List.Vector.ofFn ![fuelValue value,
        encodeState (⟨1, [visitValue value], []⟩ : State), parameter] := by
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
    · change evaluate (liftP fuel) (List.Vector.ofFn ![value,parameter]) = fuelValue value
      simpa only [liftPEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero] using fuelEvaluation value
    · change evaluate (liftP initial) (List.Vector.ofFn ![value,parameter]) =
        encodeState (⟨1, [visitValue value], []⟩ : State)
      simpa only [liftPEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero] using initialEvaluation value
    · rfl
  rw [hv, actualOriginalParameterizedEncodedResultStackIteration]

theorem runSingletonPEvaluation (guard leaf : Program 2) (combine : Program 5)
    (value parameter : Nat) :
    evaluate (runP guard leaf combine) (List.Vector.ofFn ![value,parameter]) =
      encodeState (⟨1, [], [semanticFoldP guard leaf combine value parameter]⟩ : State) := by
  rw [runPEvaluation]
  exact congrArg encodeState (actualOriginalCompletedResultFold
    (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
    (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
    (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter]))
    value [] (fuelValue value) (Nat.le_refl _))

theorem unaryCompositionEvaluation {n : Nat} (P : Program 1) (Q : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition P (fun _ : Fin 1 => Q)) v =
      evaluate P (List.Vector.ofFn ![evaluate Q v]) := by
  change evaluate P (List.Vector.ofFn fun _ : Fin 1 => evaluate Q v) = _
  congr 1

theorem actualOriginalParameterizedBoundedResultFoldCalibration :
    InternalParameterizedApplicationResultFoldCalibrationTargets.ActualOriginalParameterizedBoundedResultFoldCalibration := by
  intro guard leaf combine value parameter
  dsimp only
  constructor
  · exact runSingletonPEvaluation guard leaf combine value parameter
  · rw [foldP, unaryCompositionEvaluation, runSingletonPEvaluation, outputSingletonEvaluation]

theorem actualOriginalParameterizedResultFoldGoodRunCalibration :
    InternalParameterizedApplicationResultFoldCalibrationTargets.ActualOriginalParameterizedResultFoldGoodRunCalibration := by
  intro guard leaf combine value parameter
  rw [goodRunP, unaryCompositionEvaluation, runSingletonPEvaluation, goodStateSingletonEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
