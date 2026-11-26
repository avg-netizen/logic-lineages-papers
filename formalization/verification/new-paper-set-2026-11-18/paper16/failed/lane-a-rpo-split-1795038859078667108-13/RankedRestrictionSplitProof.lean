import LogicLineages.PersistentMarking.RankedRestrictionTargets

namespace LogicLineages.PersistentMarking.RankedRestrictionSplitProof
open Spine RankedRestrictionTargets

theorem insertLeft {ts rest ys zs : Args} {q : Expr}
    (h : Remove ts q rest) (hs : Split rest ys zs) :
    ∃ ys', Remove ys' q ys ∧ Split ts ys' zs := by
  induction h generalizing ys zs with
  | here => exact ⟨_,.here,.left hs⟩
  | there _ ih =>
    cases hs with
    | left hs =>
      obtain ⟨new,hRemove,hSplit⟩ := ih hs
      exact ⟨_,.there hRemove,.left hSplit⟩
    | right hs =>
      obtain ⟨new,hRemove,hSplit⟩ := ih hs
      exact ⟨new,hRemove,.right hSplit⟩

theorem insertRight {ts rest ys zs : Args} {q : Expr}
    (h : Remove ts q rest) (hs : Split rest ys zs) :
    ∃ zs', Remove zs' q zs ∧ Split ts ys zs' := by
  induction h generalizing ys zs with
  | here => exact ⟨_,.here,.right hs⟩
  | there _ ih =>
    cases hs with
    | left hs =>
      obtain ⟨new,hRemove,hSplit⟩ := ih hs
      exact ⟨new,hRemove,.left hSplit⟩
    | right hs =>
      obtain ⟨new,hRemove,hSplit⟩ := ih hs
      exact ⟨_,.there hRemove,.right hSplit⟩

theorem compose {xs kept removed equal changed : Args}
    (outer : Split xs kept removed) (inner : Split kept equal changed) :
    ∃ rest, Split xs equal rest ∧ Split rest removed changed := by
  induction outer generalizing equal changed with
  | nil => cases inner; exact ⟨.nil,.nil,.nil⟩
  | right _ ih =>
    obtain ⟨rest,hOuter,hInner⟩ := ih inner
    exact ⟨_,.right hOuter,.left hInner⟩
  | left _ ih =>
    cases inner with
    | left h =>
      obtain ⟨rest,hOuter,hInner⟩ := ih h
      exact ⟨rest,.left hOuter,hInner⟩
    | right h =>
      obtain ⟨rest,hOuter,hInner⟩ := ih h
      exact ⟨_,.right hOuter,.right hInner⟩

theorem atLeft {xs ys zs : Args} (h : Split xs ys zs) {i : Nat} {q : Expr} (ha : At ys i q) :
    ∃ j, At xs j q := by
  induction h generalizing i with
  | nil => cases ha
  | left _ ih =>
    cases ha with
    | here => exact ⟨0,.here⟩
    | there ha =>
      obtain ⟨j,hj⟩ := ih ha
      exact ⟨j+1,.there hj⟩
  | right _ ih =>
    obtain ⟨j,hj⟩ := ih ha
    exact ⟨j+1,.there hj⟩

theorem atRight {xs ys zs : Args} (h : Split xs ys zs) {i : Nat} {q : Expr} (ha : At zs i q) :
    ∃ j, At xs j q := by
  induction h generalizing i with
  | nil => cases ha
  | left _ ih =>
    obtain ⟨j,hj⟩ := ih ha
    exact ⟨j+1,.there hj⟩
  | right _ ih =>
    cases ha with
    | here => exact ⟨0,.here⟩
    | there ha =>
      obtain ⟨j,hj⟩ := ih ha
      exact ⟨j+1,.there hj⟩

theorem noRight {xs ys : Args} (h : Split xs ys .nil) : xs = ys := by
  induction h with
  | nil => rfl
  | left _ ih => rw [ih]

theorem atRemove {xs rest : Args} {u q : Expr} {i : Nat}
    (h : Remove xs u rest) (ha : At xs i q) :
    q = u ∨ ∃ j, At rest j q := by
  induction h generalizing i with
  | here =>
    cases ha with
    | here => exact Or.inl rfl
    | there ha => exact Or.inr ⟨_,ha⟩
  | there _ ih =>
    cases ha with
    | here => exact Or.inr ⟨0,.here⟩
    | there ha =>
      rcases ih ha with h | ⟨j,hj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j+1,.there hj⟩

theorem inheritNonempty {xs ys zs : Args} (h : Split xs ys zs) (hs : Nonempty ys) : Nonempty xs := by
  cases h with
  | nil => exact hs
  | left | right => trivial

end LogicLineages.PersistentMarking.RankedRestrictionSplitProof
