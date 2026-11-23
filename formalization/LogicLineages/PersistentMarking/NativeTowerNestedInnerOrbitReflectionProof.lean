import LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitLexProof
import LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedChecks

namespace LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitReflectionProof
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets
open NativeTowerOuterIndexConeProof NativeTowerNestedInnerOrbitLexProof

theorem exact_OriginalOrbitLexTrichotomy (k : Nat) :
    ∀ p q : OrbitCoords k, OrbitLex k p q ∨ p = q ∨ OrbitLex k q p := by
  induction k with
  | zero =>
    intro p q
    exact Nat.lt_trichotomy p q
  | succ k ih =>
    intro p q
    rcases p with ⟨p,m⟩
    rcases q with ⟨q,n⟩
    rcases ih p q with first | same | later
    · exact Or.inl (Or.inl first)
    · subst q
      rcases Nat.lt_trichotomy m n with before | eq | after
      · exact Or.inl (Or.inr ⟨rfl,before⟩)
      · subst n
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,after⟩))
    · exact Or.inr (Or.inr (Or.inl later))

private theorem noLoopOfAcc {α : Type} {r : α → α → Prop} {x : α} (h : Acc r x) :
    ¬ r x x := by
  induction h with
  | intro x _ ih =>
    intro loop
    exact ih x loop loop

theorem exact_OriginalNativeStrictNoLoop (S : Signature) (v : Base S) : ¬ NativeBelow v v :=
  noLoopOfAcc ((NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType).apply v)

theorem exact_ActualFixedTowerNestedStrictIff (S : Signature) (l k : Nat)
    (p q : OrbitCoords k) :
    NativeBelow (nestedPoint S l k p) (nestedPoint S l k q) ↔ OrbitLex k p q := by
  refine ⟨?_,exact_OriginalTowerNestedLexPreservation S l k p q⟩
  intro edge
  rcases exact_OriginalOrbitLexTrichotomy k p q with below | eq | above
  · exact below
  · rw [eq] at edge
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ edge)
  · have reverse := exact_OriginalTowerNestedLexPreservation S l k q p above
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ (transBase edge reverse))

theorem exact_ActualFixedTowerNestedInjective (S : Signature) (l k : Nat) :
    ∀ p q : OrbitCoords k, nestedPoint S l k p = nestedPoint S l k q → p = q := by
  intro p q eq
  rcases exact_OriginalOrbitLexTrichotomy k p q with below | same | above
  · have actual := exact_OriginalTowerNestedLexPreservation S l k p q below
    rw [eq] at actual
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ actual)
  · exact same
  · have actual := exact_OriginalTowerNestedLexPreservation S l k q p above
    rw [eq] at actual
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ actual)

#print axioms exact_OriginalOrbitLexTrichotomy
#print axioms exact_OriginalNativeStrictNoLoop
#print axioms exact_ActualFixedTowerNestedStrictIff
#print axioms exact_ActualFixedTowerNestedInjective

end LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitReflectionProof
