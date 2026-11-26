module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
open Source OriginalTypedDecoder OriginalTypedDecoderCalibrationProof
open OriginalTypedDecoderCalibrationValuesProof OriginalTypedDecoderTargetLeafValuesProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem guardEvaluation (n : Nat) (G : Program 1) (hG : ContextGuardCalibrated n G)
    (v : List.Vector Nat 2) :
    evaluate (.composition G (fun _ : Fin 1 => InternalApplicationCertificateConstructors.leftOf
      (.projection (1 : Fin 2)))) v =
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair (v.get 1)).1).isSome.toNat := by
  rw [unaryCompositionEvaluation,hG]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,leftOfEvaluation,projectionEvaluation]

theorem targetCheckEvaluation (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (hH : HeadSignatureCalibrated n arity H) (v : List.Vector Nat 2) :
    evaluate (.composition (termCheck H)
      ![InternalApplicationCertificateConstructors.leftOf (.projection (0 : Fin 2)),
        InternalApplicationCertificateConstructors.rightOf (.projection 0),
        InternalApplicationCertificateConstructors.rightOf (.projection 1)]) v =
      packedDecoderValue n arity (v.get 0) (Nat.unpair (v.get 1)).2 := by
  rw [ternaryCompositionEvaluation,termCalibration n arity H hH]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,leftOfEvaluation,rightOfEvaluation,projectionEvaluation]
  exact (packedValue n arity (v.get 0) (Nat.unpair (v.get 1)).2).symm

theorem actualOriginalTypedTargetLeafCalibration :
    OriginalTypedDecoderTargets.ActualOriginalTypedTargetLeafCalibration := by
  intro n arity H G hH hG v
  rw [target,InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    guardEvaluation n G hG,targetCheckEvaluation n arity H hH,targetValueEquation]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => simp
  | some context =>
    rcases packedBit n arity (v.get 0) (Nat.unpair (v.get 1)).2 with h | h <;>
      simp only [List.Vector.get_zero] at h <;> simp [h]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
