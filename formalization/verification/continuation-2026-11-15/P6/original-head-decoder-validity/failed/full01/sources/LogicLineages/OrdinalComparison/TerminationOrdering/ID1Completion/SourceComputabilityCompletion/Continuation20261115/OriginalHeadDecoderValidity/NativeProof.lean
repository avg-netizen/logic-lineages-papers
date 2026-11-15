module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedNumericDecoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open Continuation20261114.OriginalHeadEncodingBridge.NativeProof (chooseEvaluation)

theorem decoderEqualsParser (n raw : Nat) : decodeHeadNumber n raw = headParse n raw := by
  cases h : headParse n raw with
  | none => simp [decodeHeadNumber,h]
  | some head =>
    have hs := NumberedRawParserSoundnessSupportProof.headSound n raw head h
    simp [decodeHeadNumber,h,hs]

theorem basicValue (raw : Nat) : evaluate basicPayload (raw ::ᵥ nil) =
    if (Nat.unpair raw).2 = 0 then 1 else 0 := by
  simp only [basicPayload,sameOfEvaluation,rightEvaluation,constantEvaluation]
  rfl

theorem rankedValue (n raw : Nat) : evaluate (rankedPayload n) (raw ::ᵥ nil) =
    if (Nat.unpair raw).2 < n then 1 else 0 := by
  change evaluate InternalLessThan.ltTest (ofFn ![
    evaluate InternalUnpair.right (raw ::ᵥ nil),evaluate (OriginalRawSyntaxTransport.constant 1 n) (raw ::ᵥ nil)]) = _
  rw [rightEvaluation,constantEvaluation,InternalEqualityTestEvaluationProof.vectorTwo,
    InternalLessThanEvaluationProof.exactLessThanEvaluation]
  rfl

theorem nativeDecoderValidity : Targets.NativeDecoderValidity := by
  intro n raw
  change evaluate (check n) (raw ::ᵥ nil) = _
  rw [decoderEqualsParser]
  rcases hp : Nat.unpair raw with ⟨tag,payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | tag
  all_goals simp [check,chooseEvaluation,basicValue,rankedValue,constantEvaluation,
    headParse,hp,NumberedTypeCodecPrimrecSupportProof.decodeTypeExact]
  all_goals split_ifs <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
