module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
open OriginalHereditaryValidity OriginalHereditaryValidityEvaluationSupportProof
open OriginalHereditaryValidityEvaluationTransitionProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem iterateZero (oldSource oldTarget member : Program 2) (initial : Nat) :
    evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![0,initial]) = initial := rfl

theorem iterateSuccessor (oldSource oldTarget member : Program 2) (count initial : Nat) :
    evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![count + 1,initial]) =
      evaluate (transition oldSource oldTarget member) (List.Vector.ofFn ![
        evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![count,initial])]) := by
  change evaluate (transition oldSource oldTarget member) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![count,initial])) = _
  congr 1

theorem iterateEvaluation (oldSource oldTarget member : Program 2) (count initial : Nat) :
    evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![count,initial]) =
      iterateValue
        (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
        count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, actualOriginalHereditaryTransitionCalibration, ih]
    rfl

theorem fuelEvaluation (v : List.Vector Nat 2) :
    evaluate fuel v = payloadValue (v.get 0) + 1 := by
  change Nat.succ (evaluate (InternalApplicationCertificateConstructors.rightOf
    (.projection (0 : Fin 2))) v) = _
  rw [rightOfEvaluation]
  rfl

theorem initialEvaluation (v : List.Vector Nat 2) :
    evaluate initial v = initialValue (v.get 0) (v.get 1) := by
  rw [initial, pairOfEvaluation, oneEvaluation, consOfEvaluation, pairOfEvaluation,
    zeroEvaluation]
  rfl

theorem runEvaluation (oldSource oldTarget member : Program 2) (v : List.Vector Nat 2) :
    evaluate (run oldSource oldTarget member) v =
      runValue
        (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
        (v.get 0) (v.get 1) := by
  rw [run, binaryCompositionEvaluation, fuelEvaluation, initialEvaluation, iterateEvaluation]
  rfl

theorem finishedEvaluation (v : List.Vector Nat 1) :
    evaluate finished v = finishedValue (v.get 0) := by
  simp only [finished, conjunctionEvaluation, exactOneEvaluation, statusEvaluation,
    sameEvaluation, workEvaluation, zeroEvaluation, finishedValue]
  split_ifs <;> simp_all

theorem validatorEvaluation (oldSource oldTarget member : Program 2)
    (v : List.Vector Nat 2) :
    evaluate (validator oldSource oldTarget member) v =
      validatorValue
        (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
        (v.get 0) (v.get 1) := by
  rw [validator, unaryCompositionEvaluation, finishedEvaluation]
  change finishedValue (evaluate (run oldSource oldTarget member) v) = _
  rw [runEvaluation]
  rfl

theorem actualOriginalHereditaryBoundedCalibration :
    OriginalHereditaryValidityTargets.ActualOriginalHereditaryBoundedCalibration := by
  intro oldSource oldTarget member
  dsimp only
  refine ⟨iterateEvaluation oldSource oldTarget member, ?_, ?_⟩
  · intro value parameter
    exact validatorEvaluation oldSource oldTarget member (List.Vector.ofFn ![value,parameter])
  · intro v
    rw [validatorEvaluation]
    unfold validatorValue finishedValue
    split_ifs <;> simp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
