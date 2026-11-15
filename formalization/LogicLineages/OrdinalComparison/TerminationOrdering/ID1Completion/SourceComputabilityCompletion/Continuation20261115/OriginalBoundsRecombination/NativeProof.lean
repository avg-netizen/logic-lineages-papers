module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof
open NumberedNumericDecoding
open NumberedSyntaxBoundsPrimrecSupportProof

theorem nativeRecombine : Targets.NativeRecombine := by
  intro n v
  rw [recombine,evalBranch]
  change (if evaluate (OriginalCodeValidityGuard.check n) (ofFn ![v.get 0]) = 0 then 0 else
    evaluate merge (ofFn ![evaluate (root n) (ofFn ![v.get 0]),evaluate collect (ofFn ![v.get 1])]) + 1) = _
  rw [OriginalCodeValidityGuard.NativeProof.nativeValidity]
  cases hc : decodeCode n (v.get 0) with
  | none => rfl
  | some code =>
    simp only [Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,Option.map_some,Option.getD_some]
    rw [RootProof.rootAccepted n (v.get 0) code hc]
    rw [InternalEqualityTestEvaluationProof.vectorOne,ArithmeticProof.collectValue,
      InternalEqualityTestEvaluationProof.vectorTwo,ArithmeticProof.mergeValue]
    simp only [NumberedSyntaxBoundsPrimrecSupportProof.recombine,mergeBounds,
      Encodable.encode_some,ArithmeticProof.pairEncoding,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.unpair_pair]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.NativeProof
