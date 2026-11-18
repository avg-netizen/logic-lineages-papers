import LogicLineages.PersistentMarking.OwnerRefinementTargets
import LogicLineages.PersistentMarking.RefinementAppendProof
namespace LogicLineages.PersistentMarking.OwnerOccurrenceProof
open Spine

theorem prefixFacts {S : Signature} {xs ys : Args} (h : Prefix xs ys)
    (ht : ExtrasTyped EmptyContext ys) (hv : ValidArgs S ys) : ExtrasTyped EmptyContext xs ∧ ValidArgs S xs := by
  induction h with
  | nil => exact ⟨.nil,True.intro⟩
  | cons h ih =>
    cases ht with
    | cons hq hqs =>
      have hh := ih hqs hv.2
      exact ⟨.cons hq hh.1,⟨hv.1,hh.2⟩⟩

theorem prefixMember {xs ys : Args} (h : Prefix xs ys) {i q} (ha : At xs i q) : At ys i q := by
  induction h generalizing i with
  | nil => cases ha
  | cons h ih =>
    cases ha with
    | here => exact .here
    | there ha => exact .there (ih ha)

/- Restore the literal removed occurrence, including retained preceding entries. -/
theorem restore {S : Signature} {ys rest : Args} {x : Expr} (h : Remove ys x rest)
    (hx : Typed EmptyContext x x.type) (hvx : Valid S x)
    (ht : ExtrasTyped EmptyContext rest) (hv : ValidArgs S rest) : ExtrasTyped EmptyContext ys ∧ ValidArgs S ys := by
  induction h with
  | here => exact ⟨.cons hx ht,⟨hvx,hv⟩⟩
  | there h ih =>
    cases ht with
    | cons hq hqs =>
      have hh := ih hx hvx hqs hv.2
      exact ⟨.cons hq hh.1,⟨hv.1,hh.2⟩⟩

theorem permutationFacts {S : Signature} {xs ys : Args} (h : Permutation xs ys)
    (ht : ExtrasTyped EmptyContext xs) (hv : ValidArgs S xs) : ExtrasTyped EmptyContext ys ∧ ValidArgs S ys := by
  induction h with
  | nil => exact ⟨.nil,True.intro⟩
  | cons hr hp ih =>
    cases ht with
    | cons hq hqs =>
      have hh := ih hqs hv.2
      have he := SpineShiftProof.annotationExact _ _ _ hq
      exact restore hr (he.symm ▸ hq) hv.1 hh.1 hh.2

theorem removeMember {ys rest : Args} {x : Expr} (h : Remove ys x rest) {i q} (ha : At ys i q) :
    q = x ∨ ∃ j, At rest j q := by
  induction h generalizing i with
  | here =>
    cases ha with
    | here => exact Or.inl rfl
    | there h => exact Or.inr ⟨_,h⟩
  | there h ih =>
    cases ha with
    | here => exact Or.inr ⟨0,.here⟩
    | there ha =>
      rcases ih ha with he | ⟨j,hj⟩
      · exact Or.inl he
      · exact Or.inr ⟨j+1,.there hj⟩

theorem permutationMember {xs ys : Args} (h : Permutation xs ys) {i q} (ha : At ys i q) : ∃ j, At xs j q := by
  induction h generalizing i with
  | nil => cases ha
  | cons hr hp ih =>
    rcases removeMember hr ha with he | ⟨j,hj⟩
    · subst q; exact ⟨0,.here⟩
    · obtain ⟨k,hk⟩ := ih hj
      exact ⟨k+1,.there hk⟩
end LogicLineages.PersistentMarking.OwnerOccurrenceProof
