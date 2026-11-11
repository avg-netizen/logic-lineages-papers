module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderMachineCalibrationProof
open OriginalTypedDecoder OriginalTypedDecoderEvaluationSupportProof OriginalTypedDecoderSelectorProof
open OriginalTypedDecoderTransitionProof OriginalTypedDecoderEncodedProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem iterateSuccessor (H : Program 1) (count initial : Nat) :
    evaluate (iterate H) (List.Vector.ofFn ![count + 1,initial]) =
      evaluate (transition H) (List.Vector.ofFn ![
        evaluate (iterate H) (List.Vector.ofFn ![count,initial])]) := by
  change evaluate (transition H) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate H) (List.Vector.ofFn ![count,initial])) = _
  congr 1

 theorem iterateEvaluation (H : Program 1) (count initial : Nat) :
    evaluate (iterate H) (List.Vector.ofFn ![count,initial]) =
      iterateValue (programValue H) count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, transitionEvaluation]
    change transitionValue (programValue H)
      (evaluate (iterate H) (List.Vector.ofFn ![count,initial])) = _
    rw [ih]
    rfl

 theorem iterateVectorEvaluation (H : Program 1) (v : List.Vector Nat 2) :
    evaluate (iterate H) v = iterateValue (programValue H) (v.get 0) (v.get 1) := by
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := by
    rw [InternalEqualityTestEvaluationProof.vectorTwo]
    exact (List.Vector.ofFn_get v).symm.trans (InternalEqualityTestEvaluationProof.vectorTwo v.get)
  conv_lhs => rw [hv]
  exact iterateEvaluation H _ _

 theorem finishedEvaluation (v : List.Vector Nat 1) : evaluate finished v = finishedValue (v.get 0) := by
  simp only [finished, ifSameEvaluation, constantEvaluation, statusEvaluation,
    workEvaluation, finishedValue]
  split_ifs <;> simp_all

 theorem termInitialEvaluation (v : List.Vector Nat 3) :
    evaluate termInitial v = initialValue (termRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  simp only [termInitial, liveOfEvaluation, consOfEvaluation, termRequestOfEvaluation,
    constantEvaluation, projectionEvaluation, initialValue]

 theorem argumentsInitialEvaluation (v : List.Vector Nat 3) :
    evaluate argumentsInitial v = initialValue (argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  simp only [argumentsInitial, liveOfEvaluation, consOfEvaluation, argumentsRequestOfEvaluation,
    constantEvaluation, projectionEvaluation, initialValue]

 theorem termRunEvaluation (H : Program 1) (v : List.Vector Nat 3) :
    evaluate (termRun H) v = iterateValue (programValue H) (v.get 1 + 1)
      (initialValue (termRequestValue (v.get 2) (v.get 0) (v.get 1))) := by
  rw [termRun, binaryCompositionEvaluation, iterateEvaluation, termInitialEvaluation]
  rfl

 theorem argumentsRunEvaluation (H : Program 1) (v : List.Vector Nat 3) :
    evaluate (argumentsRun H) v = iterateValue (programValue H) (v.get 1 + 1)
      (initialValue (argumentsRequestValue (v.get 2) (v.get 0) (v.get 1))) := by
  rw [argumentsRun, binaryCompositionEvaluation, iterateEvaluation, argumentsInitialEvaluation]
  rfl

 theorem termCheckEvaluation (H : Program 1) (v : List.Vector Nat 3) :
    evaluate (termCheck H) v =
      checkValue (programValue H) (termRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  rw [termCheck, unaryCompositionEvaluation, finishedEvaluation]
  change finishedValue (evaluate (termRun H) v) = _
  rw [termRunEvaluation]
  simp only [checkValue, requestRaw, termRequestValue, Nat.unpair_pair]

 theorem argumentsCheckEvaluation (H : Program 1) (v : List.Vector Nat 3) :
    evaluate (argumentsCheck H) v =
      checkValue (programValue H) (argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  rw [argumentsCheck, unaryCompositionEvaluation, finishedEvaluation]
  change finishedValue (evaluate (argumentsRun H) v) = _
  rw [argumentsRunEvaluation]
  simp only [checkValue, requestRaw, argumentsRequestValue, Nat.unpair_pair]

 theorem actualOriginalTypedMachineCalibration :
    OriginalTypedDecoderTargets.ActualOriginalTypedMachineCalibration :=
  ⟨transitionEvaluation, encodedTransition, iterateVectorEvaluation, finishedEvaluation,
    fun H v => ⟨termCheckEvaluation H v, argumentsCheckEvaluation H v⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderMachineCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderMachineCalibrationProof
