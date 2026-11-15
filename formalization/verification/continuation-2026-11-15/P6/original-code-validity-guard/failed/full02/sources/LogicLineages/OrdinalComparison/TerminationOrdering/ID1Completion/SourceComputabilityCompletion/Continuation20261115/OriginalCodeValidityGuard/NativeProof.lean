module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem boolGet (xs : List Bool) (index : Nat) :
    (xs.map Bool.toNat).getD index 0 = (xs.getD index false).toNat := by
  induction xs generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index

theorem nativeValidity : Targets.NativeValidity := by
  intro n raw
  change evaluate InternalRawListRecursion.lookup (ofFn ![raw,
    evaluate (OriginalCodeDecoderTable.tableProgram n) (ofFn ![raw+1,raw])]) = _
  rw [OriginalCodeDecoderTable.NativeProof.nativeTable]
  simp only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,
    Continuation20261114.ExchangeAnswerSlots.NativeProof.lookupEncoded,boolGet]
  have h := NumberedCodeParserTableSupportProof.calibration n raw (raw+1) raw (Nat.le_refl raw)
  change (NumberedCodeParserTable.lookup (NumberedCodeParserTable.codeTable n raw (raw+1)) raw).toNat = _
  rw [h,NumberedCodeParserTableSupportProof.validatedSuccess]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.NativeProof
