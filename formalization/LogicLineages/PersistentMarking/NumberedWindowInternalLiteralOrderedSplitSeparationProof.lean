module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitRefutationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralJUnionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitSeparationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (direct directLists readWitness)
open NumberedWindowInternalLiteralOrderedSplitNumericProof
  (scalar relation checker)
open NumberedWindowInternalLiteralOrderedSplitRefutationProof
  (installed exact_NotLiteralOrderedMultisetSplit)
open NumberedWindowInternalDirectCoreCalibrationProof (exact_OriginalDirectCoreNumeric)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowFunctionalOrderedSplitBoundaryProof (allScalars noInsertions)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open ConditionalJUnionTargets (CarrierUnion UnionClosure MultisetSplit)

def StrictDeletion (dst src : Nat) : Prop :=
  ∃ witness, evaluate checker (src ::ᵥ witness ::ᵥ dst ::ᵥ nil) = 1

def rawLength (code : Nat) : Nat := ((unpack code).getD []).length

private theorem deletionDecreases {dst src : Nat} (h : StrictDeletion dst src) :
    rawLength dst < rawLength src := by
  obtain ⟨w,h⟩ := h
  rw [checker,exact_OriginalDirectCoreNumeric scalar relation permutation allScalars noInsertions
    (fun _ => rfl) (fun _ _ _ => rfl) exact_OriginalLiteralCountFit] at h
  unfold direct at h
  cases hs : unpack src <;> cases hw : readWitness w <;> cases ht : unpack dst <;>
    rw [hs,hw,ht] at h <;> try contradiction
  rename_i xs wit ys
  have directTrue : directLists allScalars noInsertions xs ys wit = true := by
    cases good : directLists allScalars noInsertions xs ys wit <;> simp_all
  rcases wit with ⟨kept,removed,added⟩
  simp only [directLists,Bool.and_eq_true] at directTrue
  rcases directTrue with ⟨⟨⟨⟨⟨_,_⟩,before⟩,after⟩,nonempty⟩,noadd⟩
  have nothing : added = [] := by
    cases ha : added with
    | nil => rfl
    | cons a as => simp [ha,noInsertions] at noadd
  have positiveLength : 0 < removed.length := by
    cases removed with
    | nil => simp at nonempty
    | cons x xs => exact Nat.zero_lt_succ _
  have b := (of_decide_eq_true before).length_eq
  have a := (of_decide_eq_true after).length_eq
  simp only [rawLength,hs,ht,Option.getD_some]
  rw [b,a,nothing]
  simp only [List.map_nil,List.append_nil,List.length_append]
  exact Nat.lt_add_of_pos_right positiveLength

/-- The counterexample needs no ill-founded edge or artificial
arithmetic interpretation: every accepted edge deletes at least one
literal occurrence, and the installed direct relation is well-founded. -/
theorem exact_LiteralDeletionWellFounded : WellFounded StrictDeletion :=
  (measure rawLength).wf.mono (fun _ _ => deletionDecreases)

/-- Carrier preservation and J closure hold on the same literal body
that refutes the exact functional ordered split. -/
theorem exact_LiteralUnionClosureWithoutOrderedSplit (c : Nat) :
    CarrierUnion installed c functionalUnion ∧ UnionClosure installed c functionalUnion ∧
      ¬ MultisetSplit installed c functionalUnion := by
  exact ⟨NumberedWindowInternalFunctionalLiteralCarrierProof.exact_FunctionalLiteralCarrierUnion scalar relation c,
    NumberedWindowInternalFunctionalLiteralJUnionProof.exact_FunctionalLiteralJUnion scalar relation c,
    exact_NotLiteralOrderedMultisetSplit c⟩

#print axioms exact_LiteralDeletionWellFounded
#print axioms exact_LiteralUnionClosureWithoutOrderedSplit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitSeparationProof
