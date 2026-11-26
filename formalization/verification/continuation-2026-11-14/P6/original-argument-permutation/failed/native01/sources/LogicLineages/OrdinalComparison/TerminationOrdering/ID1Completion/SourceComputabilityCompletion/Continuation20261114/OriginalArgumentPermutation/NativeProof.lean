module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open ArgumentEntriesLayer.NativeProof (encodeNone encodeSome encodeNil encodeCons)

theorem listEncoding {A : Type} [Encodable A] (xs : List A) :
    Encodable.encode xs = numbersNumber (xs.map Encodable.encode) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [encodeCons,List.map_cons,numbersNumber,ih]

theorem leftValue (n : Nat) (base target : Code (Fin n)) :
    evaluate leftEntries (ofFn ![codeNumber base,codeNumber target]) = Encodable.encode (NumberedExchangeCode.argumentEntries base) :=
  ArgumentEntriesRecursor.Proof.originalExtraction n base 0

theorem rightValue (n : Nat) (base target : Code (Fin n)) :
    evaluate rightEntries (ofFn ![codeNumber base,codeNumber target]) = Encodable.encode (NumberedExchangeCode.argumentEntries target) :=
  ArgumentEntriesRecursor.Proof.originalExtraction n target 0

theorem comparisonValue (v : List.Vector Nat 2) :
    evaluate compare v = evaluate ArgumentCountComparison.permutation
      (ofFn ![evaluate leftEntries v - 1,evaluate rightEntries v - 1]) := by
  rw [compare,binaryCompositionEvaluation,leftList,rightList,
    predecessorCompositionEvaluation,predecessorCompositionEvaluation]

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n base target
  rw [check,evalBranch,leftValue]
  cases hs : NumberedExchangeCode.argumentEntries base with
  | none => simp only [encodeNone,ite_true,constantEvaluation,NumberedExchangeCode.argumentPermutation,hs,Bool.toNat_false]
  | some xs =>
    simp only [encodeSome,Nat.add_one_ne_zero,ite_false]
    rw [evalBranch,rightValue]
    cases ht : NumberedExchangeCode.argumentEntries target with
    | none => simp only [encodeNone,ite_true,constantEvaluation,NumberedExchangeCode.argumentPermutation,hs,ht,Bool.toNat_false]
    | some ys =>
      simp only [encodeSome,Nat.add_one_ne_zero,ite_false]
      rw [comparisonValue,leftValue,rightValue,hs,ht,encodeSome,encodeSome,Nat.add_sub_cancel,Nat.add_sub_cancel,
        listEncoding,listEncoding]
      exact (ArgumentCountComparison.NativeProof.nativePermutation).2 n xs ys

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.NativeProof
