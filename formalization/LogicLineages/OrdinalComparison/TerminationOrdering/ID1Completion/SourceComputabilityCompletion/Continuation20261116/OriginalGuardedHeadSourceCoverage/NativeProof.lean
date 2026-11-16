module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation conjunctionEvaluation)
open NumberedLeastCodeRepresentative NumberedNumericDecoding
open Continuation20261114 Continuation20261115
open NativeSelectorsProof

theorem headCanonical (n raw : Nat) (head : NumberedAuxiliaryCoding.HeadCode (Fin n))
    (h : decodeHeadNumber n raw = some head) : headNumber head = raw := by
  simp only [decodeHeadNumber,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

theorem value (n : Nat) (arity : Fin n → Nat) (head context : Nat) :
    evaluate (window n arity) (ofFn ![head,context]) = OriginalUniverseDecoder.headWindowValue n arity head context := by
  rw [window,conjunctionEvaluation,conjunctionEvaluation,contextValue,headValue]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context with
  | none => simp [hc,OriginalUniverseDecoder.headWindowValue]
  | some ctx =>
    cases hh : decodeHeadNumber n head with
    | none => simp [hc,hh,OriginalUniverseDecoder.headWindowValue]
    | some h =>
      have he := headCanonical n head h hh
      have ce := OriginalClassCodes.NativeCodecProof.contextCanonical n context ctx hc
      have hr : evaluate (rawWindow n arity) (ofFn ![head,context]) =
          (decide (NumberedFiniteUniverse.HeadInWindow arity ctx.1.1 ctx.1.2
            (NumberedAuxiliaryDecoding.decodeHead h))).toNat := by
        rw [← he,← ce,rawEncoded]
      rw [hr]
      simp only [hc,hh,Option.isSome_some,Bool.toNat_true,OriginalUniverseDecoder.headWindowValue]
      cases decide (NumberedFiniteUniverse.HeadInWindow arity ctx.1.1 ctx.1.2
        (NumberedAuxiliaryDecoding.decodeHead h)) <;> rfl

theorem nativeOriginalWindow : Targets.NativeOriginalWindow := by
  intro n arity v
  have hv : v = ofFn ![v.get 0,v.get 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  exact value n arity (v.get 0) (v.get 1)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeProof
