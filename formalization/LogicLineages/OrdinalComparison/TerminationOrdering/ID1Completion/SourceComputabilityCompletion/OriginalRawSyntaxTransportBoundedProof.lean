module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBoundedProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportStateEvaluationProof OriginalRawSyntaxTransportTransitionProof
open OriginalRawSyntaxTransportWeightProof (fuelEvaluation)
open InternalApplicationResultStackEvaluationProof
  (liveOfEvaluation statusEvaluation workEvaluation resultsEvaluation headOfEvaluation tailOfEvaluation)
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem iterateSuccessor (mode : Mode) (count initial : Nat) :
    evaluate (iterate mode) (List.Vector.ofFn ![count + 1,initial]) =
      evaluate (transition mode) (List.Vector.ofFn ![
        evaluate (iterate mode) (List.Vector.ofFn ![count,initial])]) := by
  change evaluate (transition mode) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate mode) (List.Vector.ofFn ![count,initial])) = _
  congr 1

 theorem iterateEvaluation (mode : Mode) (count initial : Nat) :
    evaluate (iterate mode) (List.Vector.ofFn ![count,initial]) = iterateValue mode count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, actualRawSyntaxTransitionCalibration, ih]
    rfl

 theorem initialEvaluation (v : List.Vector Nat 3) :
    evaluate initial v = initialValue (v.get 0) (v.get 1) (v.get 2) := by
  rw [initial, liveOfEvaluation, consOfEvaluation, visitOfEvaluation, constantEvaluation]
  rfl

 theorem runEvaluation (mode : Mode) (v : List.Vector Nat 3) :
    evaluate (run mode) v = runValue mode (v.get 0) (v.get 1) (v.get 2) := by
  rw [run, binaryCompositionEvaluation, fuelEvaluation, initialEvaluation, iterateEvaluation]
  rfl

 theorem outputEvaluation (v : List.Vector Nat 1) : evaluate output v = outputValue (v.get 0) := by
  simp only [output, InternalApplicationResultStack.output, evalBranch,
    InternalApplicationValidityStackEvaluationProof.exactOneEvaluation,
    statusEvaluation, workEvaluation, resultsEvaluation, headOfEvaluation,
    tailOfEvaluation, zeroEvaluation, outputValue]
  split_ifs <;> simp_all

 theorem foldEvaluation (mode : Mode) (v : List.Vector Nat 3) :
    evaluate (fold mode) v = foldValue mode (v.get 0) (v.get 1) (v.get 2) := by
  rw [fold, unaryCompositionEvaluation, outputEvaluation]
  change outputValue (evaluate (run mode) v) = _
  rw [runEvaluation]
  rfl

 theorem actualRawSyntaxBoundedCalibration : OriginalRawSyntaxTransportTargets.ActualRawSyntaxBoundedCalibration := by
  refine ⟨iterateEvaluation, ?_, ?_⟩
  · intro state
    exact outputEvaluation (List.Vector.ofFn ![state])
  · intro mode d k raw
    exact ⟨runEvaluation mode (List.Vector.ofFn ![d,k,raw]), foldEvaluation mode (List.Vector.ofFn ![d,k,raw])⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBoundedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBoundedProof
