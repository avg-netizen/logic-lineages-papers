module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.NativeProof
open Continuation20261115
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem nativeConvertedValidity : Targets.NativeConvertedValidity := by
  intro n encoded
  rw [OriginalEncodedHeadConversion.NativeProof.nativeConversion]
  cases h : (Encodable.decode encoded : Option (HeadCode (Fin n))) with
  | none =>
    change (decodeHeadNumber n (headNumber (HeadCode.zero : HeadCode (Fin n)))).isSome = true
    rw [NumberedNumericDecodingSupportProof.headNumericRoundTrip]
    rfl
  | some head =>
    change (decodeHeadNumber n (headNumber head)).isSome = true
    rw [NumberedNumericDecodingSupportProof.headNumericRoundTrip]
    rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.NativeProof
