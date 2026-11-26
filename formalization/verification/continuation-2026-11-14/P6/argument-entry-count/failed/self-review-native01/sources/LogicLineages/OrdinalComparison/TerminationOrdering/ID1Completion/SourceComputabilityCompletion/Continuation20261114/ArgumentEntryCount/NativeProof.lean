module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import Mathlib.Data.List.Count
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem stepValue (head acc needle : Nat) :
    evaluate step (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = if head = needle then acc+1 else acc := by
  rw [step,evalBranch,evalNormalize,sameOfEvaluation]
  have h0 : evaluate (.projection (0 : Fin 3)) (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = head := rfl
  have h2 : evaluate (.projection (2 : Fin 3)) (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = needle := rfl
  rw [h0,h2]
  by_cases h : head=needle <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]
  all_goals rfl

theorem foldCount (xs : List Nat) (needle : Nat) :
    xs.foldr (fun head acc => evaluate step (head ::ᵥ acc ::ᵥ needle ::ᵥ nil)) 0 = xs.count needle := by
  induction xs with
  | nil => rfl
  | cons head xs ih =>
    rw [List.foldr_cons,stepValue,ih]
    by_cases h : head=needle <;> simp [List.count_cons,h,eq_comm]

theorem numericCount (xs : List Nat) (needle : Nat) :
    evaluate count (ofFn ![numbersNumber xs,needle]) = xs.count needle := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (constant 1 0) step (needle ::ᵥ nil) (numbersNumber xs)
  change evaluate count (ofFn ![numbersNumber xs,needle]) = _ at h
  rw [h,numbersRoundTrip]
  exact foldCount xs needle

theorem nativeCount : Targets.NativeCount := by
  constructor
  · exact numericCount
  · intro n xs needle
    rw [numericCount]
    exact List.count_map_of_injective xs Encodable.encode Encodable.encode_injective needle

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.NativeProof
