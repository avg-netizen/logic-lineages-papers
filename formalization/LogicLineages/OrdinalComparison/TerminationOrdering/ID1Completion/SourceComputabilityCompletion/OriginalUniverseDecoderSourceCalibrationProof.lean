module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderNumericCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderMachineCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderSourceCalibrationProof
open Source OriginalUniverseDecoder OriginalUniverseDecoderNumericCalibrationProof
open OriginalUniverseDecoderMachineCalibrationProof OriginalUniverseDecoderReconstructionProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem calibratedMemberFunction (n : Nat) (M : Program 2) (hM : ContextMemberCalibrated n M) :
    programValue2 M = contextMemberValue n := by
  funext typ context
  exact hM (List.Vector.ofFn ![typ,context])

theorem calibratedWindowFunction (n : Nat) (arity : Fin n → Nat) (W : Program 2)
    (hW : HeadWindowCalibrated n arity W) : programValue2 W = headWindowValue n arity := by
  funext head context
  exact hW (List.Vector.ofFn ![head,context])

theorem termCheckCalibration (n : Nat) (arity : Fin n → Nat) (H : Program 1) (M W : Program 2)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hM : ContextMemberCalibrated n M) (hW : HeadWindowCalibrated n arity W)
    (v : List.Vector Nat 4) :
    evaluate (termCheck H M W) v = checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity)
      (OriginalTypedDecoder.termRequestValue (v.get 2) (v.get 0) (v.get 1)) (v.get 3) := by
  rw [termCheckEvaluation,OriginalTypedDecoderCalibrationProof.calibratedHeadFunction n arity H hH,
    calibratedMemberFunction n M hM,calibratedWindowFunction n arity W hW]

theorem quaternaryCompositionEvaluation {n : Nat} (p : Program 4) (q r s t : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r,s,t]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v,evaluate s v,evaluate t v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 4 => evaluate (![q,r,s,t] i) v) = _
  congr 1

theorem contextGuardEvaluation (n : Nat) (G : Program 1)
    (hG : OriginalTypedDecoder.ContextGuardCalibrated n G) (v : List.Vector Nat 2) :
    evaluate (.composition G ![InternalApplicationCertificateConstructors.leftOf (.projection 1)]) v =
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1).isSome.toNat := by
  rw [unaryVectorCompositionEvaluation,hG]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,leftOfEvaluation,projectionEvaluation]

theorem sourceCheckEvaluation (n : Nat) (arity : Fin n → Nat) (H : Program 1) (M W : Program 2)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hM : ContextMemberCalibrated n M) (hW : HeadWindowCalibrated n arity W) (v : List.Vector Nat 2) :
    evaluate (.composition (termCheck H M W)
      ![InternalApplicationCertificateConstructors.leftOf (.projection 0),
        InternalApplicationCertificateConstructors.rightOf (.projection 0),
        InternalApplicationCertificateConstructors.rightOf (.projection 1),
        InternalApplicationCertificateConstructors.leftOf (.projection 1)]) v =
      checkValue (OriginalTypedDecoder.headSignatureValue n arity)
        (contextMemberValue n) (headWindowValue n arity)
        (OriginalTypedDecoder.termRequestValue (Nat.unpair (v.get 1)).2
          (Nat.unpair (v.get 0)).1 (Nat.unpair (v.get 0)).2) (Nat.unpair (v.get 1)).1 := by
  rw [quaternaryCompositionEvaluation,termCheckCalibration n arity H M W hH hM hW]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    leftOfEvaluation,rightOfEvaluation,projectionEvaluation]

theorem sourceCalibration (n : Nat) (arity : Fin n → Nat) (H G : Program 1) (M W : Program 2)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalTypedDecoder.ContextGuardCalibrated n G)
    (hM : ContextMemberCalibrated n M) (hW : HeadWindowCalibrated n arity W)
    (v : List.Vector Nat 2) :
    evaluate (source H G M W) v = InternalOriginalUniformParameterLeaves.sourceValue n arity v := by
  rw [source,InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    contextGuardEvaluation n G hG,sourceCheckEvaluation n arity H M W hH hM hW]
  obtain ⟨Gamma,hGamma⟩ := OriginalTypedDecoderCodecProof.contextEncodingSurjective (Nat.unpair (v.get 1)).2
  have ho := OriginalTypedDecoderTargetLeafValuesProof.parameterObjectEncoded (v.get 0) (v.get 1) Gamma hGamma
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none => simp [InternalOriginalUniformParameterLeaves.sourceValue,
      InternalOriginalUniformParameterLeaves.decodedValue,hc]
  | some ctx =>
    have he := OriginalUniverseDecoderContextCodecProof.outerContextDecodeSound n _ ctx hc
    have hv := packedNumericCalibration n arity ctx Gamma (v.get 0)
    rw [he,hGamma] at hv
    rw [hv,NumberedUniverseNumericValidationProof.rawCarrierValidation]
    simp only [InternalOriginalUniformParameterLeaves.sourceValue,
      InternalOriginalUniformParameterLeaves.decodedValue,hc,ho]
    cases NumberedNumericCarrier.rawCarrierTest n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) <;> rfl

theorem actualOriginalUniverseSourceCalibration :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseSourceCalibration := by
  intro n arity H G M W hH hG hM hW
  refine ⟨sourceCalibration n arity H G M W hH hG hM hW,?_⟩
  intro typ raw gamma context
  rw [termCheckCalibration n arity H M W hH hM hW]
  exact termReconstruction n arity typ raw gamma context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderSourceCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderSourceCalibrationProof
