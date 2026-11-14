module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem stepValue (head acc : Nat) (left right : List Nat) :
    evaluate step (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) =
      if left.count head = right.count head then acc else 0 := by
  have hl : evaluate leftCount (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) = left.count head :=
    ArgumentEntryCount.NativeProof.numericCount left head
  have hr : evaluate rightCount (head ::ᵥ acc ::ᵥ numbersNumber left ::ᵥ numbersNumber right ::ᵥ nil) = right.count head :=
    ArgumentEntryCount.NativeProof.numericCount right head
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

theorem nativeBounded : Targets.NativeBounded := by
  intro candidates left right
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
  have ha := PrimaryExpansion.NativeProof.appendEvaluation (numbersNumber left) right
  rw [numbersRoundTrip] at ha
  simp only [Option.getD_some] at ha
  change evaluate allCounts (ofFn ![evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![numbersNumber left,numbersNumber right]),numbersNumber left,numbersNumber right]) = _
  rw [ha,nativeBounded]
  by_cases hp : left.Perm right
  · have hb := (boundedIff left right).mpr hp
    simp only [hp,hb,decide_true]
  · have hb : ¬ (∀ a ∈ left ++ right, left.count a = right.count a) := fun h => hp ((boundedIff left right).mp h)
    simp only [hp,hb,decide_false]

theorem nativePermutation : Targets.NativePermutation := by
  constructor
  · exact numericPermutation
  · intro n left right
    rw [numericPermutation]
    have h : (left.map Encodable.encode).Perm (right.map Encodable.encode) ↔ left.Perm right := by
      constructor
      · intro h
        apply List.perm_iff_count.mpr
        intro a
        have hc := List.perm_iff_count.mp h (Encodable.encode a)
        simpa only [List.count_map_of_injective _ _ Encodable.encode_injective] using hc
      · intro h
        exact h.map Encodable.encode
    by_cases hp : left.Perm right
    · have hm := h.mpr hp
      simp only [hp,hm,decide_true]
    · have hm : ¬ (left.map Encodable.encode).Perm (right.map Encodable.encode) := fun hm => hp (h.mp hm)
      simp only [hp,hm,decide_false]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.NativeProof
