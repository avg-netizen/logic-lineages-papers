import LogicLineages.PersistentMarking.FullPrefixOrderOrbitProof
import LogicLineages.PersistentMarking.NativeIndexedCarrierChecks
import LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype

namespace LogicLineages.PersistentMarking.NativeIndexedFullPrefixOrderOrbitProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierSubtype
open FullPrefixOrderOrbitProof

variable {I V : Type*}

def indexCarrier {S : Signature} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A))
    (e : I → ClosedNativeTerm S indexType) (i : I) : ClosedNativeTerm S (actualType A) :=
  indexedTerm A P U (e i)

/-- All three order edges are those of the actual indexed carrier, with
the same original step, seed, and embedded indices throughout. -/
theorem exact_ActualIndexedFullPrefixEdges {S : Signature} {r : I → I → Prop}
    (A : SemanticType) (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (e : I → ClosedNativeTerm S indexType)
    (preserve : ∀ j i, r j i → NativeBelow (e j) (e i)) :
    CarrierEdges r (@NativeBelow S (actualType A)) (indexCarrier A P U e) (fun u => applyClosed P u) U := by
  have original (i : I) := NativeIndexedCarrierChecks.exact_IndexedCarrier S A P.val U.val (e i).val
    P.property U.property (e i).property
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (original i).1
  · intro j i strict
    exact ((original i).2 (e j).val (e j).property (preserve j i strict)).1
  · intro j i strict
    exact ((original i).2 (e j).val (e j).property (preserve j i strict)).2

/-- Conditional order-indexed form of the original carrier inference.
The realization laws are genuine supplied semantic data, not replacements
for the source relation or claims of completed ordinal semantics. -/
theorem exact_OriginalNativeIndexedFullPrefixOrbit [LE V]
    {S : Signature} {r : I → I → Prop} (wf : WellFounded r) (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (e : I → ClosedNativeTerm S indexType)
    (preserve : ∀ j i, r j i → NativeBelow (e j) (e i))
    {f : V → V} {x : V} {orbit : I → V}
    {realizes : ClosedNativeTerm S (actualType A) → V → Prop}
    (equations : FullPrefixEquations r f x orbit)
    (laws : RealizationLaws r (@NativeBelow S (actualType A)) (fun u => applyClosed P u) f realizes)
    (seedValue : realizes U x) :
    ∀ i j, (j = i ∨ r j i) → realizes (indexedTerm A P U (e i)) (orbit j) :=
  exact_FullPrefixCarrierAllApproached wf equations
    (exact_ActualIndexedFullPrefixEdges A P U e preserve) laws seedValue

#print axioms exact_ActualIndexedFullPrefixEdges
#print axioms exact_OriginalNativeIndexedFullPrefixOrbit

end LogicLineages.PersistentMarking.NativeIndexedFullPrefixOrderOrbitProof
