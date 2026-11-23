import LogicLineages.PersistentMarking.NativeIndexedCarrierFiniteOrbitProof
import LogicLineages.PersistentMarking.StablePairProof

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierOrbitBlocksProof
open Spine NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierTargets
open NativeIndexedCarrierSubtype NativeOrdinalBasisTargets NativeIndexedCarrierFiniteOrbitProof

private theorem strictTrans {S B} {x y z : ClosedNativeTerm S B}
    (xy : NativeBelow x y) (yz : NativeBelow y z) : NativeBelow x z :=
  StablePairProof.strictTransitive S z.val y.val x.val yz xy

/-- The original empty-call Select directly picks the original second argument
of a same-typed native application, with the original support inclusion. -/
theorem exact_SameTypedNativeApplicationSelect {S B}
    (P : ClosedNativeTerm S (.arrow B B)) (u : ClosedNativeTerm S B) :
    NativeBelow u (applyClosed P u) := by
  let expr := applyClosed P u
  change ConfinedPair.Strict S expr.val u.val
  exact ⟨⟨B,expr.property.1.1,u.property.1.1,expr.property.1.2.1,u.property.1.2.1⟩,
    .intro expr.property.1.1 u.property.1.1 rfl
      (NativeTypingProof.secondSelect S B B P.val u.val .nil
        P.property.1.1 u.property.1.1 u.property.1.2.1 .nil True.intro),
    NativeTypingProof.rightIncluded B B P.val u.val⟩

private theorem orbitLe {S B} (P : ClosedNativeTerm S (.arrow B B)) (u : ClosedNativeTerm S B)
    {a b : Nat} (h : a ≤ b) :
    finiteApplication P u a = finiteApplication P u b ∨
      NativeBelow (finiteApplication P u a) (finiteApplication P u b) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step n _ ih =>
    have next := exact_SameTypedNativeApplicationSelect P (finiteApplication P u n)
    refine Or.inr ?_
    rcases ih with same | before
    · rw [same]
      exact next
    · exact strictTrans before next

theorem exact_SameTypedNativeFiniteOrbitStrict {S B}
    (P : ClosedNativeTerm S (.arrow B B)) (u : ClosedNativeTerm S B)
    {m n : Nat} (increase : m < n) :
    NativeBelow (finiteApplication P u m) (finiteApplication P u n) := by
  have next : NativeBelow (finiteApplication P u m) (finiteApplication P u (m+1)) :=
    exact_SameTypedNativeApplicationSelect P (finiteApplication P u m)
  rcases orbitLe P u (show m+1 ≤ n from increase) with same | after
  · rw [← same]
    exact next
  · exact strictTrans next after

/-- Each original index carries its literal higher-typed orbit, rather than a
separately generated block pretending to be a native iterator result. -/
def indexedOrbitBlock {S} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType) (n : Nat) :
    ClosedNativeTerm S (actualType A) :=
  finiteApplication P (indexedTerm A P U i) n

theorem exact_IndexedOrbitBlockSeparation {S} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i j : ClosedNativeTerm S indexType)
    (earlier : NativeBelow i j) (m n : Nat) :
    NativeBelow (indexedOrbitBlock A P U i m) (indexedOrbitBlock A P U j n) := by
  have before : NativeBelow (indexedOrbitBlock A P U i m) (indexedTerm A P U j) :=
    exact_IndexedCarrierFiniteEarlierOrbit A P U j i earlier m
  rcases orbitLe P (indexedTerm A P U j) (Nat.zero_le n) with same | after
  · change NativeBelow (indexedOrbitBlock A P U i m) (finiteApplication P (indexedTerm A P U j) n)
    rw [← same]
    exact before
  · exact strictTrans before after

#print axioms exact_SameTypedNativeApplicationSelect
#print axioms exact_SameTypedNativeFiniteOrbitStrict
#print axioms exact_IndexedOrbitBlockSeparation

end LogicLineages.PersistentMarking.NativeIndexedCarrierOrbitBlocksProof
