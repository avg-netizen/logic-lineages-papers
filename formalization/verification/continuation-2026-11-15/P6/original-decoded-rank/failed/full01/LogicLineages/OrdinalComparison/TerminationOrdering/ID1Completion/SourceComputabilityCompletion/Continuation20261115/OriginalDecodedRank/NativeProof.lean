module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedNumericDecoding
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open OriginalDecodedDependencies.NativeProof

theorem nativeOriginalRank : Targets.NativeOriginalRank := by
  intro n v
  unfold rank
  rw [evalBranch]
  simp only [OriginalDecodedDependencies.accepted,conjunctionEvaluation,sourceAcceptedValue,targetAcceptedValue,
    constantEvaluation,sourceValue,Continuation20261114.ExchangeNumericSuppliers.rankValue,
    Continuation20261114.ExchangeNumericSuppliers.rankAt,nodeDecode]
  cases hs : decodeCode n (Nat.unpair (v.get 0)).1 with
  | none => simp [hs]
  | some a =>
    cases ht : decodeCode n (Nat.unpair (v.get 0)).2 with
    | none => simp [hs,ht]
    | some c =>
      simp only [hs,ht,Option.isSome_some,Bool.toNat_true,ite_true,Option.bind_some,Option.map_some,Option.getD_some]
      exact (NumberedNumericDecodingProof.codeNumericSound n _ a hs).symm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.NativeProof
