module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderFuelProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderMachineCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderMachineCalibrationProof
open OriginalUniverseDecoder OriginalUniverseDecoderGuardEvaluationProof
open OriginalTypedDecoderEvaluationSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem unaryVectorCompositionEvaluation {n : Nat} (p : Program 1) (q : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q]) v = evaluate p (List.Vector.ofFn ![evaluate q v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 1 => evaluate (![q] i) v) = _
  congr 1

theorem transitionEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 2) :
    evaluate (transition H M W) v = transitionValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W) (v.get 0) (v.get 1) := by
  simp only [transition,ifSameEvaluation,evalBranch,constantEvaluation,
    binaryCompositionEvaluation,unaryVectorCompositionEvaluation,guardEvaluation,
    OriginalTypedDecoderTransitionProof.transitionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    headOfEvaluation,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,transitionValue]

theorem iterateSuccessor (H : Program 1) (M W : Program 2) (count initial context : Nat) :
    evaluate (iterate H M W) (List.Vector.ofFn ![count+1,initial,context]) =
      evaluate (transition H M W) (List.Vector.ofFn
        ![evaluate (iterate H M W) (List.Vector.ofFn ![count,initial,context]),context]) := by
  change evaluate (transition H M W) (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (![Program.projection (1 : Fin 4),Program.projection (3 : Fin 4)] i)
      (List.Vector.ofFn ![count,evaluate (iterate H M W)
        (List.Vector.ofFn ![count,initial,context]),initial,context])) = _
  congr 1

theorem iterateEvaluation (H : Program 1) (M W : Program 2) (count initial context : Nat) :
    evaluate (iterate H M W) (List.Vector.ofFn ![count,initial,context]) =
      iterateValue (OriginalTypedDecoder.programValue H) (programValue2 M) (programValue2 W)
        count initial context := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor,transitionEvaluation]
    change transitionValue (OriginalTypedDecoder.programValue H) (programValue2 M) (programValue2 W)
      (evaluate (iterate H M W) (List.Vector.ofFn ![count,initial,context])) context = _
    rw [ih]
    rfl

theorem iterateVectorEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 3) :
    evaluate (iterate H M W) v = iterateValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W) (v.get 0) (v.get 1) (v.get 2) := by
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1,v.get 2] := by
    rw [InternalEqualityTestEvaluationProof.vectorThree]
    exact (List.Vector.ofFn_get v).symm.trans (InternalEqualityTestEvaluationProof.vectorThree v.get)
  conv_lhs => rw [hv]
  exact iterateEvaluation H M W _ _ _

theorem termInitialEvaluation (v : List.Vector Nat 4) :
    evaluate termInitial v = OriginalTypedDecoder.initialValue
      (OriginalTypedDecoder.termRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  simp only [termInitial,liveOfEvaluation,consOfEvaluation,termRequestOfEvaluation,
    constantEvaluation,projectionEvaluation,OriginalTypedDecoder.initialValue]

theorem argumentsInitialEvaluation (v : List.Vector Nat 4) :
    evaluate argumentsInitial v = OriginalTypedDecoder.initialValue
      (OriginalTypedDecoder.argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)) := by
  simp only [argumentsInitial,liveOfEvaluation,consOfEvaluation,argumentsRequestOfEvaluation,
    constantEvaluation,projectionEvaluation,OriginalTypedDecoder.initialValue]

theorem termRunEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 4) :
    evaluate (termRun H M W) v =
      iterateValue (OriginalTypedDecoder.programValue H) (programValue2 M) (programValue2 W)
        (v.get 1+1) (OriginalTypedDecoder.initialValue
          (OriginalTypedDecoder.termRequestValue (v.get 2) (v.get 0) (v.get 1))) (v.get 3) := by
  rw [termRun,ternaryCompositionEvaluation,iterateEvaluation,termInitialEvaluation]
  rfl

theorem argumentsRunEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 4) :
    evaluate (argumentsRun H M W) v =
      iterateValue (OriginalTypedDecoder.programValue H) (programValue2 M) (programValue2 W)
        (v.get 1+1) (OriginalTypedDecoder.initialValue
          (OriginalTypedDecoder.argumentsRequestValue (v.get 2) (v.get 0) (v.get 1))) (v.get 3) := by
  rw [argumentsRun,ternaryCompositionEvaluation,iterateEvaluation,argumentsInitialEvaluation]
  rfl

theorem termCheckEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 4) :
    evaluate (termCheck H M W) v = checkValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W)
      (OriginalTypedDecoder.termRequestValue (v.get 2) (v.get 0) (v.get 1)) (v.get 3) := by
  rw [termCheck,unaryVectorCompositionEvaluation,OriginalTypedDecoderMachineCalibrationProof.finishedEvaluation]
  change OriginalTypedDecoder.finishedValue (evaluate (termRun H M W) v) = _
  rw [termRunEvaluation]
  simp only [checkValue,OriginalTypedDecoder.requestRaw,OriginalTypedDecoder.termRequestValue,Nat.unpair_pair]

theorem argumentsCheckEvaluation (H : Program 1) (M W : Program 2) (v : List.Vector Nat 4) :
    evaluate (argumentsCheck H M W) v = checkValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W)
      (OriginalTypedDecoder.argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)) (v.get 3) := by
  rw [argumentsCheck,unaryVectorCompositionEvaluation,OriginalTypedDecoderMachineCalibrationProof.finishedEvaluation]
  change OriginalTypedDecoder.finishedValue (evaluate (argumentsRun H M W) v) = _
  rw [argumentsRunEvaluation]
  simp only [checkValue,OriginalTypedDecoder.requestRaw,OriginalTypedDecoder.argumentsRequestValue,Nat.unpair_pair]

theorem actualOriginalUniverseMachineCalibration :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseMachineCalibration :=
  ⟨transitionEvaluation,OriginalUniverseDecoderEncodedProof.encodedTransition,
    iterateVectorEvaluation,fun H M W v => ⟨termCheckEvaluation H M W v,argumentsCheckEvaluation H M W v⟩,
    OriginalUniverseDecoderFuelProof.singletonFuel⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderMachineCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderMachineCalibrationProof
