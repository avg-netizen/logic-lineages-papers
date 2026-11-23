import LogicLineages.PersistentMarking.NativeOrdinalCapHierarchyBoundsProof
import LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedChecks

namespace LogicLineages.PersistentMarking.NativeOrdinalCapHierarchyLexProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalBasisTargets NativeOrdinalCapPathsTargets
open NativeOrdinalCapHierarchyBoundsProof

/-- Highest coordinate first: each lower block gets a separate, strictly
separated interval, not an assumed monotone transport of argument slots. -/
def StrictLex : (d : Nat) → Coordinates d → Coordinates d → Prop
  | 0, _, _ => False
  | d + 1, p, q => p.1 < q.1 ∨ (p.1 = q.1 ∧ StrictLex d p.2 q.2)

theorem exact_NativeCapHierarchyLexPreservation (S : Signature) (d : Nat) :
    ∀ (u : BaseTerm S) (p q : Coordinates d),
      StrictLex d p q → NativeBelow (blockAt S d p u) (blockAt S d q u) := by
  induction d with
  | zero => intro u p q smaller; exact False.elim smaller
  | succ d ih =>
    intro u p q smaller
    change p.1 < q.1 ∨ (p.1 = q.1 ∧ StrictLex d p.2 q.2) at smaller
    let vp := finiteApplication (capLevel S d) u p.1
    let vq := finiteApplication (capLevel S d) u q.1
    change NativeBelow (blockAt S d p.2 vp) (blockAt S d q.2 vq)
    rcases smaller with earlier | ⟨same,lower⟩
    · have before := (exact_CapHierarchyFloorCeiling S d p.2 vp).2
      have after := (exact_CapHierarchyFloorCeiling S d q.2 vq).1
      have between : NativeLe (applyClosed (capLevel S d) vp) vq :=
        iterationLe S d u earlier
      exact strictLe (strictLe before between) after
    · have sameBase : vp = vq := congrArg (finiteApplication (capLevel S d) u) same
      rw [sameBase]
      exact ih vq p.2 q.2 lower

theorem lexTrichotomy (d : Nat) :
    ∀ (p q : Coordinates d), StrictLex d p q ∨ p = q ∨ StrictLex d q p := by
  induction d with
  | zero =>
    intro p q
    cases p
    cases q
    exact Or.inr (Or.inl rfl)
  | succ d ih =>
    intro p q
    rcases p with ⟨m,p⟩
    rcases q with ⟨n,q⟩
    rcases Nat.lt_trichotomy m n with earlier | same | later
    · exact Or.inl (Or.inl earlier)
    · subst n
      rcases ih p q with smaller | eq | greater
      · exact Or.inl (Or.inr ⟨rfl,smaller⟩)
      · subst q
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,greater⟩))
    · exact Or.inr (Or.inr (Or.inl later))

private theorem noLoopOfAcc {α : Type} {r : α → α → Prop} {x : α} (h : Acc r x) :
    ¬ r x x := by
  induction h with
  | intro y _ ih =>
    intro loop
    exact ih y loop loop

private theorem noLoop (S : Signature) (v : BaseTerm S) : ¬ NativeBelow v v :=
  noLoopOfAcc ((NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType).apply v)

theorem exact_NativeCapHierarchyLexReflection (S : Signature) (d : Nat)
    (u : BaseTerm S) (p q : Coordinates d) :
    NativeBelow (blockAt S d p u) (blockAt S d q u) ↔ StrictLex d p q := by
  refine ⟨?_,exact_NativeCapHierarchyLexPreservation S d u p q⟩
  intro strict
  rcases lexTrichotomy d p q with smaller | eq | greater
  · exact smaller
  · subst q
    exact False.elim (noLoop S _ strict)
  · have opposite := exact_NativeCapHierarchyLexPreservation S d u q p greater
    exact False.elim (noLoop S _ (strictComp strict opposite))

theorem exact_NativeCapHierarchyInjective (S : Signature) (d : Nat) (u : BaseTerm S) :
    ∀ (p q : Coordinates d), blockAt S d p u = blockAt S d q u → p = q := by
  intro p q eq
  rcases lexTrichotomy d p q with smaller | same | greater
  · have lower := exact_NativeCapHierarchyLexPreservation S d u p q smaller
    rw [eq] at lower
    exact False.elim (noLoop S _ lower)
  · exact same
  · have lower := exact_NativeCapHierarchyLexPreservation S d u q p greater
    rw [eq] at lower
    exact False.elim (noLoop S _ lower)

#print axioms exact_NativeCapHierarchyLexPreservation
#print axioms exact_NativeCapHierarchyLexReflection
#print axioms exact_NativeCapHierarchyInjective

end LogicLineages.PersistentMarking.NativeOrdinalCapHierarchyLexProof
