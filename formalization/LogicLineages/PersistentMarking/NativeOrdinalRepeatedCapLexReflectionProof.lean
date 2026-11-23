import LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexEmbeddingProof

namespace LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexReflectionProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalRepeatedCapLexEmbeddingProof

private theorem noLoopOfAcc {α : Type} {r : α → α → Prop} {x : α} (h : Acc r x) :
    ¬ r x x := by
  induction h with
  | intro y _ ih =>
    intro loop
    exact ih y loop loop

private theorem noLoop (S : Signature) (v : ClosedNativeTerm S indexType) : ¬ NativeBelow v v :=
  noLoopOfAcc ((NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType).apply v)

private theorem noOpposite (S : Signature) (v w : ClosedNativeTerm S indexType)
    (h : NativeBelow v w) (k : NativeBelow w v) : False :=
  noLoop S v (StablePairProof.strictTransitive S v.val w.val v.val k h)

/-- The induced order on the actual block images is precisely lexicographic.
The reverse direction uses actual original asymmetry, not just a monotone
enumeration or a comparison invented on the range. -/
theorem exact_ActualNativeBlockStrictIff (S : Signature)
    (u : ClosedNativeTerm S indexType) (p q : Nat × Nat) :
    NativeBelow (blockImage S u p) (blockImage S u q) ↔ BlockLex p q := by
  refine ⟨?_,exact_ActualNativeBlockLexPreservation S u p q⟩
  rcases p with ⟨k,m⟩
  rcases q with ⟨l,n⟩
  intro strict
  rcases Nat.lt_trichotomy k l with less | eq | greater
  · exact Or.inl less
  · subst l
    rcases Nat.lt_trichotomy m n with less | eq | greater
    · exact Or.inr ⟨rfl,less⟩
    · subst n
      exact False.elim (noLoop S _ strict)
    · have back := exact_ActualNativeBlockLexPreservation S u (k,n) (k,m) (Or.inr ⟨rfl,greater⟩)
      exact False.elim (noOpposite S _ _ strict back)
  · have back := exact_ActualNativeBlockLexPreservation S u (l,n) (k,m) (Or.inl greater)
    exact False.elim (noOpposite S _ _ strict back)

#print axioms exact_ActualNativeBlockStrictIff

end LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexReflectionProof
