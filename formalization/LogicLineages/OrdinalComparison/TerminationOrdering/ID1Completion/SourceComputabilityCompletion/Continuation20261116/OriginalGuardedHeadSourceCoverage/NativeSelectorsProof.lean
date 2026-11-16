module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation conjunctionEvaluation)
open NumberedLeastCodeRepresentative NumberedNumericDecoding
open Continuation20261114 Continuation20261115

theorem symbolsValue (context : Nat) :
    evaluate contextSymbols (ofFn ![context]) = (Nat.unpair (Nat.unpair context).1).1 := by
  rw [contextSymbols,unaryCompositionEvaluation,leftEvaluation,leftEvaluation]
  rfl

theorem symbolsEncoded (n : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) :
    evaluate contextSymbols (ofFn ![Encodable.encode ctx]) = Encodable.encode ctx.1.1 := by
  rw [symbolsValue]
  change (Nat.unpair (Nat.unpair (Nat.pair
    (Nat.pair (Encodable.encode ctx.1.1) (Encodable.encode ctx.1.2))
    (Encodable.encode ctx.2))).1).1 = Encodable.encode ctx.1.1
  rw [Nat.unpair_pair,Nat.unpair_pair]

theorem rawValue (n : Nat) (arity : Fin n → Nat) (head context : Nat) :
    evaluate (rawWindow n arity) (ofFn ![head,context]) =
      evaluate (OriginalHeadWindow.window n arity)
        (ofFn ![head,evaluate contextSymbols (ofFn ![context]),
          evaluate OriginalUniverseDomainCoverage.contextTypes (ofFn ![context])]) := by
  rw [rawWindow,ternaryCompositionEvaluation]
  simp only [unaryCompositionEvaluation,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem rawEncoded (n : Nat) (arity : Fin n → Nat)
    (head : NumberedAuxiliaryCoding.HeadCode (Fin n)) (ctx : OrdinaryArithmeticQuotient.Context n) :
    evaluate (rawWindow n arity) (ofFn ![headNumber head,Encodable.encode ctx]) =
      (decide (NumberedFiniteUniverse.HeadInWindow arity ctx.1.1 ctx.1.2
        (NumberedAuxiliaryDecoding.decodeHead head))).toNat := by
  rw [rawValue,symbolsEncoded,OriginalUniverseDomainCoverage.NativeProof.typesEncoded,
    OriginalClassCodes.NativeCodecProof.symbolNumbers,OriginalContextInsertionCalibrationProof.contextNumbers]
  exact OriginalHeadWindow.NativeProof.nativeWindow n arity ctx.1.1 ctx.1.2 head

theorem contextValue (n head context : Nat) :
    evaluate (.composition (OriginalDecodedContextValidity.contextGuard n)
      (fun _ : Fin 1 => .projection 1)) (ofFn ![head,context]) =
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context).isSome.toNat := by
  rw [unaryCompositionEvaluation,OriginalDecodedContextValidity.NativeProof.nativeContext]
  rfl

theorem headValue (n head context : Nat) :
    evaluate (.composition (OriginalHeadDecoderValidity.check n)
      (fun _ : Fin 1 => .projection 0)) (ofFn ![head,context]) =
      (decodeHeadNumber n head).isSome.toNat := by
  rw [unaryCompositionEvaluation]
  change evaluate (OriginalHeadDecoderValidity.check n) (ofFn ![head]) = _
  exact OriginalHeadDecoderValidity.NativeProof.nativeDecoderValidity n head

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeSelectorsProof
