module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderMachineCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open OriginalTypedDecoder OriginalTypedDecoderCalibrationValuesProof
open OriginalTypedDecoderMachineCalibrationProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem calibratedHeadFunction (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : HeadSignatureCalibrated n arity H) : programValue H = headSignatureValue n arity := by
  funext value
  exact hH (List.Vector.ofFn ![value])

theorem termCalibration (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : HeadSignatureCalibrated n arity H) (v : List.Vector Nat 3) :
    evaluate (termCheck H) v = termDecoderValue n arity (v.get 0) (v.get 1) (v.get 2) := by
  rw [termCheckEvaluation,calibratedHeadFunction n arity H hH,termValue]

theorem argumentsCalibration (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : HeadSignatureCalibrated n arity H) (v : List.Vector Nat 3) :
    evaluate (argumentsCheck H) v = argumentsDecoderValue n arity (v.get 0) (v.get 1) (v.get 2) := by
  rw [argumentsCheckEvaluation,calibratedHeadFunction n arity H hH,argumentsValue]

theorem packedCalibration (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : HeadSignatureCalibrated n arity H) (v : List.Vector Nat 2) :
    evaluate (packedCheck H) v = packedDecoderValue n arity (v.get 0) (v.get 1) := by
  rw [packedCheck,ternaryCompositionEvaluation,termCalibration n arity H hH]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,leftOfEvaluation,rightOfEvaluation,projectionEvaluation]
  exact (packedValue n arity (v.get 0) (v.get 1)).symm

theorem actualOriginalTypedDecoderCalibration :
    OriginalTypedDecoderTargets.ActualOriginalTypedDecoderCalibration := by
  intro n arity H hH
  refine ⟨fun v => ⟨termCalibration n arity H hH v,argumentsCalibration n arity H hH v⟩,
    packedCalibration n arity H hH,?_,?_⟩
  · intro typ raw gamma
    rw [termCalibration n arity H hH]
    exact termReconstruction n arity typ raw gamma
  · intro types raw gamma
    rw [argumentsCalibration n arity H hH]
    exact argumentsReconstruction n arity types raw gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
