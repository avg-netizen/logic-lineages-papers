module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionListProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedExpansion NumberedMultisetNumeric
open InternalRawListRecursionEvaluationProof

theorem dropNil (k : Nat) : evaluate InternalRawListRecursion.drop (k ::ᵥ 0 ::ᵥ nil) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dropSuccessor,ih]; rfl

theorem lookupNumbers (xs : List Nat) (k : Nat) :
    evaluate InternalRawListRecursion.lookup (k ::ᵥ numbersNumber xs ::ᵥ nil) = xs[k]?.getD 0 := by
  induction xs generalizing k with
  | nil => rw [numbersNumber,lookupEvaluation,dropNil]; rfl
  | cons x xs ih =>
    cases k with
    | zero => rw [numbersNumber,lookupConsZero]; rfl
    | succ k => rw [numbersNumber,lookupConsSuccessor,ih]; rfl

theorem rangeRetrieve (xs : List Nat) :
    (List.range xs.length).map (fun k => xs[k]?.getD 0) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,OriginalHereditaryExpansionDeletionProof.rangeFront,List.map_cons,List.map_map]
    change x :: (List.range xs.length).map (fun k => xs[k]?.getD 0) = x :: xs
    rw [ih]

theorem forgetting : OriginalHereditaryAnnotatedExpansionTargets.Forgetting := by
  intro role typ raw jobs
  unfold values
  rw [List.map_map]
  have hf : (forgetNumber ∘ (fun k => decoratedValue k role typ raw (jobs[k]?.getD 0))) =
      (fun k => jobs[k]?.getD 0) := by
    funext k
    simp only [Function.comp_apply,forgetNumber,decoratedValue,jobNumber,Nat.unpair_pair]
  rw [hf,rangeRetrieve]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionListProof
