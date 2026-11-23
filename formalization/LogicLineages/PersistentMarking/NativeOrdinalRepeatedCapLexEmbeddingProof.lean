import LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockProof
import LogicLineages.PersistentMarking.StablePairProof
import LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedChecks

namespace LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexEmbeddingProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeOrdinalCapPathsTargets
open NativeOrdinalRepeatedCapBlockTargets NativeOrdinalRepeatedCapBlockProof

/-- The first coordinate chooses the actual cap block, the second chooses
the original successor occurrence inside that block. -/
def BlockLex (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

def blockImage (S : Signature) (u : ClosedNativeTerm S indexType) (p : Nat × Nat) :
    ClosedNativeTerm S indexType := blockNode S u p.1 p.2

/-- A strictly positive path composes in the actual confined strict
relation, not in a new relation defined for these witnesses. -/
theorem exact_NativePositivePathStrict {S : Signature} {n : Nat}
    {a b : ClosedNativeTerm S indexType} (p : StrictPath S n a b) :
    n ≠ 0 → NativeBelow b a := by
  induction p with
  | nil a =>
    intro nonzero
    exact False.elim (nonzero rfl)
  | @cons n a b c edge rest ih =>
    intro _
    cases n with
    | zero =>
      cases rest
      exact edge
    | succ n =>
      exact StablePairProof.strictTransitive S a.val b.val c.val edge (ih (Nat.succ_ne_zero n))

theorem exact_ActualNativeBlockLexPreservation (S : Signature)
    (u : ClosedNativeTerm S indexType) (p q : Nat × Nat) :
    BlockLex p q → NativeBelow (blockImage S u p) (blockImage S u q) := by
  rcases p with ⟨k,m⟩
  rcases q with ⟨l,n⟩
  intro h
  rcases h with earlier | ⟨same,smaller⟩
  · change k < l at earlier
    obtain ⟨d, rfl⟩ : ∃ d, l = k + (d + 1) := ⟨l - (k + 1), by omega⟩
    exact exact_NativePositivePathStrict (exact_AcrossBlockPaths S u k m d n)
      (by omega)
  · change k = l at same
    subst l
    change m < n at smaller
    obtain ⟨d, rfl⟩ : ∃ d, n = m + (d + 1) := ⟨n - (m + 1), by omega⟩
    exact exact_NativePositivePathStrict (exact_WithinBlockPaths S u k m d)
      (by omega)

private theorem lexTrichotomy (p q : Nat × Nat) : BlockLex p q ∨ p = q ∨ BlockLex q p := by
  rcases p with ⟨k,m⟩
  rcases q with ⟨l,n⟩
  rcases Nat.lt_trichotomy k l with low | eq | high
  · exact Or.inl (Or.inl low)
  · subst l
    rcases Nat.lt_trichotomy m n with low | eq | high
    · exact Or.inl (Or.inr ⟨rfl,low⟩)
    · subst n
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,high⟩))
  · exact Or.inr (Or.inr (Or.inl high))

private theorem noLoopOfAcc {α : Type} {r : α → α → Prop} {x : α} (a : Acc r x) :
    ¬ r x x := by
  induction a with
  | intro y _ ih =>
    intro loop
    exact ih y loop loop

private theorem nativeNoLoop (S : Signature) (v : ClosedNativeTerm S indexType) :
    ¬ NativeBelow v v :=
  noLoopOfAcc ((NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType).apply v)

theorem exact_ActualNativeBlockImageInjective (S : Signature) (u : ClosedNativeTerm S indexType) :
    Function.Injective (blockImage S u) := by
  intro p q same
  rcases lexTrichotomy p q with low | eq | high
  · have h := exact_ActualNativeBlockLexPreservation S u p q low
    rw [same] at h
    exact False.elim (nativeNoLoop S _ h)
  · exact eq
  · have h := exact_ActualNativeBlockLexPreservation S u q p high
    rw [same] at h
    exact False.elim (nativeNoLoop S _ h)

#print axioms exact_NativePositivePathStrict
#print axioms exact_ActualNativeBlockLexPreservation
#print axioms exact_ActualNativeBlockImageInjective

end LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexEmbeddingProof
