module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalPairingEvaluationProof InternalListCodecEvaluationProof

theorem singletonValue (index previous : Nat) :
    evaluate singleton (index ::ᵥ previous ::ᵥ nil) = numbersNumber [index] := by
  change evaluate InternalListCodec.consCode (ofFn ![index,0]) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo,consEvaluation]
  rfl

theorem stepValue (index : Nat) (previous : List Nat) :
    evaluate step (index ::ᵥ numbersNumber previous ::ᵥ nil) =
      numbersNumber (previous ++ [index]) := by
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![numbersNumber previous,evaluate singleton (index ::ᵥ numbersNumber previous ::ᵥ nil)]) = _
  rw [singletonValue,Continuation20261114.OriginalSourceHeads.RawProof.appendValue]

theorem rangeValue (bound : Nat) :
    evaluate range (bound ::ᵥ nil) = numbersNumber (List.range bound) := by
  change Nat.rec (motive := fun _ => Nat) 0
    (fun index previous => evaluate step (index ::ᵥ previous ::ᵥ nil)) bound = _
  induction bound with
  | zero => rfl
  | succ bound ih =>
    change evaluate step (bound ::ᵥ Nat.rec (motive := fun _ => Nat) 0
      (fun index previous => evaluate step (index ::ᵥ previous ::ᵥ nil)) bound ::ᵥ nil) = _
    rw [ih,stepValue,List.range_succ]

theorem natListEncoding (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [Encodable.encode_list_cons,ih]
    simp only [Encodable.encode_nat]
    rfl

theorem nativeRange : Targets.NativeRange := by
  intro v
  rw [natListEncoding]
  have h := rangeValue (v.get 0)
  have hv : v = v.get 0 ::ᵥ nil := by
    apply List.Vector.ext
    intro i
    fin_cases i
    rfl
  rw [hv]
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.NativeProof
