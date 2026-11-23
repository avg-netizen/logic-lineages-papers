import LogicLineages.PersistentMarking.NativeIndexedCarrierChecks
import LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype
import LogicLineages.PersistentMarking.NativeOrdinalBasisTargets

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierFiniteOrbitProof
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeIndexedCarrierSubtype NativeOrdinalBasisTargets

private theorem selectedSeedAndAbsorb {S : Signature} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType) :
    NativeBelow U (indexedTerm A P U i) ∧
    ∀ v : ClosedNativeTerm S (actualType A), NativeBelow v (indexedTerm A P U i) →
      NativeBelow (applyClosed P v) (indexedTerm A P U i) := by
  have hK := NativeIndexedTypingThinProof.kClosed S A P.val i.val P.property i.property
  have selectP := NativeIndexedSelectorProof.selectP S A P.val i.val P.property i.property
  have weak := ElementaryProof.strictIncluded S (K A P.val i.val) P.val selectP.2.1
  obtain ⟨base,absorb⟩ := NativeCarrierThinChecks.exact_Carrier S (actualType A)
    P.val (K A P.val i.val) U.val P.property hK U.property weak selectP.2.2
  exact ⟨base,fun v current => absorb v.val v.property.1 current.2.2 current⟩

/-- Exact finite iterations preserve membership in the strict lower cone of the
same original indexed carrier. No comparison between two iterates is asserted. -/
theorem exact_IndexedCarrierFiniteAbsorption {S : Signature} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U v : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType)
    (start : NativeBelow v (indexedTerm A P U i)) (n : Nat) :
    NativeBelow (finiteApplication P v n) (indexedTerm A P U i) := by
  induction n with
  | zero => exact start
  | succ n ih => exact (selectedSeedAndAbsorb A P U i).2 (finiteApplication P v n) ih

theorem exact_IndexedCarrierFiniteSeedOrbit {S : Signature} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType) (n : Nat) :
    NativeBelow (finiteApplication P U n) (indexedTerm A P U i) :=
  exact_IndexedCarrierFiniteAbsorption A P U U i (selectedSeedAndAbsorb A P U i).1 n

theorem exact_IndexedCarrierFiniteEarlierOrbit {S : Signature} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i j : ClosedNativeTerm S indexType)
    (earlier : NativeBelow j i) (n : Nat) :
    NativeBelow (finiteApplication P (indexedTerm A P U j) n) (indexedTerm A P U i) := by
  have strict : NativeBelow (indexedTerm A P U j) (indexedTerm A P U i) :=
    ((NativeIndexedCarrierChecks.exact_IndexedCarrier S A P.val U.val i.val
      P.property U.property i.property).2 j.val j.property earlier).1
  exact exact_IndexedCarrierFiniteAbsorption A P U (indexedTerm A P U j) i strict n

#print axioms exact_IndexedCarrierFiniteAbsorption
#print axioms exact_IndexedCarrierFiniteSeedOrbit
#print axioms exact_IndexedCarrierFiniteEarlierOrbit

end LogicLineages.PersistentMarking.NativeIndexedCarrierFiniteOrbitProof
