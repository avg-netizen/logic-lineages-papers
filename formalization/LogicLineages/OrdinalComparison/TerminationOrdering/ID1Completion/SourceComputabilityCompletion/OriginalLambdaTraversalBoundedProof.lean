module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBoundedProof
open OriginalLambdaTraversal OriginalLambdaTraversalStateEvaluationProof
open OriginalLambdaTraversalTransitionProof
open OriginalHereditaryValidityEvaluationSupportProof
  (unaryCompositionEvaluation binaryCompositionEvaluation exactOneEvaluation)
open InternalApplicationResultStackEvaluationProof
  (liveOfEvaluation statusEvaluation workEvaluation resultsEvaluation headOfEvaluation tailOfEvaluation)
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem iterateSuccessor (leaf : Program 2) (count initial : Nat) :
    evaluate (iterate leaf) (List.Vector.ofFn ![count + 1,initial]) =
      evaluate (transition leaf) (List.Vector.ofFn ![
        evaluate (iterate leaf) (List.Vector.ofFn ![count,initial])]) := by
  change evaluate (transition leaf) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate leaf) (List.Vector.ofFn ![count,initial])) = _
  congr 1

theorem iterateEvaluation (leaf : Program 2) (count initial : Nat) :
    evaluate (iterate leaf) (List.Vector.ofFn ![count,initial]) =
      iterateValue (fun value parameter => evaluate leaf (List.Vector.ofFn ![value,parameter]))
        count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, actualOriginalLambdaTraversalTransitionCalibration, ih]
    rfl

theorem fuelEvaluation (v : List.Vector Nat 2) :
    evaluate fuel v = fuelValue (v.get 0) := by
  change evaluate InternalApplicationResultStack.fuel
    (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  change evaluate InternalApplicationResultStack.fuel (List.Vector.ofFn ![v.get 0]) = _
  exact InternalApplicationResultStackStateProof.fuelEvaluation (v.get 0)

theorem initialEvaluation (v : List.Vector Nat 2) :
    evaluate initial v = initialValue (v.get 0) (v.get 1) := by
  rw [initial, liveOfEvaluation, consOfEvaluation, visitOfEvaluation, zeroEvaluation]
  rfl

theorem runEvaluation (leaf : Program 2) (v : List.Vector Nat 2) :
    evaluate (run leaf) v =
      runValue (fun value parameter => evaluate leaf (List.Vector.ofFn ![value,parameter]))
        (v.get 0) (v.get 1) := by
  rw [run, binaryCompositionEvaluation, fuelEvaluation, initialEvaluation, iterateEvaluation]
  rfl

theorem outputEvaluation (v : List.Vector Nat 1) :
    evaluate output v = outputValue (v.get 0) := by
  simp only [output, InternalApplicationResultStack.output, evalBranch,
    InternalApplicationValidityStackEvaluationProof.exactOneEvaluation,
    statusEvaluation, workEvaluation, resultsEvaluation, headOfEvaluation,
    tailOfEvaluation, zeroEvaluation, outputValue]
  split_ifs <;> simp_all

theorem foldEvaluation (leaf : Program 2) (v : List.Vector Nat 2) :
    evaluate (fold leaf) v =
      foldValue (fun value parameter => evaluate leaf (List.Vector.ofFn ![value,parameter]))
        (v.get 0) (v.get 1) := by
  rw [fold, unaryCompositionEvaluation, outputEvaluation]
  change outputValue (evaluate (run leaf) v) = _
  rw [runEvaluation]
  rfl

theorem actualOriginalLambdaTraversalBoundedCalibration :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalBoundedCalibration := by
  intro leaf
  dsimp only
  refine ⟨iterateEvaluation leaf, ?_, ?_⟩
  · intro state
    exact outputEvaluation (List.Vector.ofFn ![state])
  · intro value parameter
    exact ⟨runEvaluation leaf (List.Vector.ofFn ![value,parameter]),
      foldEvaluation leaf (List.Vector.ofFn ![value,parameter])⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBoundedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBoundedProof
