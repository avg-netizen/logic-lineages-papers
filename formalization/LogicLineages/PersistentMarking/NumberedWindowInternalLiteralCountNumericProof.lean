module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
import Mathlib.Data.List.Count

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumeric
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open ID1Completion.SourceComputabilityCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedWindowInternalLiteralCount
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorTwo)
open NumberedWindowInternalDirectCoreNumericTargets (CountFit)

private theorem entryStepValue (head acc needle : Nat) :
    evaluate entryStep (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = if head = needle then acc+1 else acc := by
  rw [entryStep,evalBranch,sameOfEvaluation]
  have h0 : evaluate (.projection (0 : Fin 3)) (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = head := rfl
  have h2 : evaluate (.projection (2 : Fin 3)) (head ::ᵥ acc ::ᵥ needle ::ᵥ nil) = needle := rfl
  rw [h0,h2]
  by_cases h : head=needle <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]
  all_goals rfl

theorem foldCount (xs : List Nat) (needle : Nat) :
    xs.foldr (fun head acc => evaluate entryStep (head ::ᵥ acc ::ᵥ needle ::ᵥ nil)) 0 = xs.count needle := by
  induction xs with
  | nil => rfl
  | cons head xs ih =>
    rw [List.foldr_cons,entryStepValue,ih]
    by_cases h : head=needle <;> simp [List.count_cons,h,eq_comm]

theorem numericCount (xs : List Nat) (needle : Nat) :
    evaluate entryCount (ofFn ![numbersNumber xs,needle]) = xs.count needle := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (constant 1 0) entryStep (needle ::ᵥ nil) (numbersNumber xs)
  change evaluate entryCount (ofFn ![numbersNumber xs,needle]) = _ at h
  rw [h,numbersRoundTrip]
  exact foldCount xs needle

private theorem appendFold (xs ys : List Nat) :
    xs.foldr (fun head rest => 1 + Nat.pair head rest) (numbersNumber ys) = numbersNumber (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

private theorem literalAppendEvaluation (front : Nat) (ys : List Nat) :
    evaluate InternalApplicationValidityStackAppend.append (ofFn ![front,numbersNumber ys]) =
      numbersNumber (((decodeNumbers front).getD []) ++ ys) := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (.projection 0) InternalApplicationValidityStackAppend.appendStep (numbersNumber ys ::ᵥ nil) front
  change evaluate InternalApplicationValidityStackAppend.append (ofFn ![front,numbersNumber ys]) = _ at h
  rw [h]
  have hs (head rest : Nat) : evaluate InternalApplicationValidityStackAppend.appendStep
      (head ::ᵥ rest ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair head rest := by
    exact InternalListCodecEvaluationProof.consEvaluation head rest
  simp only [hs]
  exact appendFold _ ys

theorem stepValue (head acc : Nat) (left right : List Nat) :
    evaluate step (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) =
      if left.count head = right.count head then acc else 0 := by
  have hl : evaluate leftCount (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) = left.count head :=
    numericCount left head
  have hr : evaluate rightCount (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) = right.count head :=
    numericCount right head
  rw [step,evalBranch,sameOfEvaluation,hl,hr]
  by_cases h : left.count head = right.count head <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]
  all_goals rfl

theorem foldValue (candidates left right : List Nat) :
    candidates.foldr (fun head acc => evaluate step (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil)) 1 =
      (decide (∀ a ∈ candidates, left.count a = right.count a)).toNat := by
  induction candidates with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldr_cons,stepValue,ih]
    by_cases h : left.count head = right.count head <;> simp [h]

theorem nativeBounded (candidates left right : List Nat) :
    evaluate allCounts (ofFn ![numbersNumber candidates,numbersNumber left,numbersNumber right]) =
      (decide (∀ a ∈ candidates, left.count a = right.count a)).toNat := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    2 (constant 2 1) step (numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) (numbersNumber candidates)
  change evaluate allCounts (ofFn ![numbersNumber candidates,numbersNumber left,numbersNumber right]) = _ at h
  rw [h,numbersRoundTrip]
  exact foldValue candidates left right

theorem boundedIff (left right : List Nat) :
    (∀ a ∈ left ++ right, left.count a = right.count a) ↔ left.Perm right := by
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro a
    by_cases ha : a ∈ left ++ right
    · exact h a ha
    · have hl : a ∉ left := fun h => ha (List.mem_append_left _ h)
      have hr : a ∉ right := fun h => ha (List.mem_append_right _ h)
      simp [List.count_eq_zero_of_not_mem hl,List.count_eq_zero_of_not_mem hr]
  · intro h a _
    exact List.perm_iff_count.mp h a

theorem numericPermutation (left right : List Nat) :
    evaluate permutation (ofFn ![numbersNumber left,numbersNumber right]) = (decide (left.Perm right)).toNat := by
  have ha := literalAppendEvaluation (numbersNumber left) right
  rw [numbersRoundTrip] at ha
  simp only [Option.getD_some] at ha
  change evaluate allCounts (ofFn ![evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![numbersNumber left,numbersNumber right]),numbersNumber left,numbersNumber right]) = _
  rw [ha,nativeBounded]
  by_cases hp : left.Perm right
  · have hb := (boundedIff left right).mpr hp
    rw [decide_eq_true hb,decide_eq_true hp]
  · have hb : ¬ (∀ a ∈ left ++ right, left.count a = right.count a) := fun h => hp ((boundedIff left right).mp h)
    simp only [hp,hb,decide_false]

theorem exactLiteralCountFit : CountFit permutation := by
  intro left right
  have h := numericPermutation left right
  rw [vectorTwo] at h
  exact h

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumeric
