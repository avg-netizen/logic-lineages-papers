import LogicLineages.PersistentMarking.NativeIndexedFullPrefixOrderOrbitProof
import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandReflectionProof
import LogicLineages.PersistentMarking.NativeCanonicalAppliedIteratorCarrierProof

namespace LogicLineages.PersistentMarking.NativeTowerBandFullPrefixIterationProof
open Spine NativeIndexedCarrierTargets NativeIteratorTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeIndexedCarrierSubtype NativeTowerWitnessFamilyProof
open FullPrefixOrderOrbitProof NativeIndexedFullPrefixOrderOrbitProof
open NativeTowerVariableDimensionBandsProof NativeTowerVariableDimensionBandReflectionProof
open NativeCanonicalAppliedIteratorCarrierProof

variable {V : Type*} [LE V]

/-- The entire verified dependent variable-dimension band sum supplies the
native indices. The original printed tower itself is one physical top at
which all of these approached orbit values are realized. -/
theorem exact_OriginalTowerBandFullPrefixCarrierRealization (S : Signature) (l : Nat) (A : SemanticType)
    (P : ClosedNativeTerm S (functionType A)) (U : ClosedNativeTerm S (actualType A))
    {f : V → V} {x : V} {orbit : BandCoords → V}
    {realizes : ClosedNativeTerm S (actualType A) → V → Prop}
    (equations : FullPrefixEquations BandLex f x orbit)
    (laws : RealizationLaws BandLex (@NativeBelow S (actualType A)) (fun u => applyClosed P u) f realizes)
    (seedValue : realizes U x) :
    (∀ i j, (j = i ∨ BandLex j i) → realizes (indexedTerm A P U (bandImage S l i)) (orbit j)) ∧
    (∀ j, realizes (indexedTerm A P U (closedTower S (l+2))) (orbit j)) := by
  have approached : ∀ i j, (j = i ∨ BandLex j i) →
      realizes (indexedTerm A P U (bandImage S l i)) (orbit j) :=
    exact_OriginalNativeIndexedFullPrefixOrbit (exact_OriginalBandLexWellFounded S l)
      A P U (bandImage S l) (exact_OriginalTowerBandLexPreservation S l) equations laws seedValue
  refine ⟨approached,?_⟩
  intro j
  have indexBelow : NativeBelow (bandImage S l j) (closedTower S (l+2)) :=
    (exact_OriginalTowerVariableDimensionLexSum S l).1 j
  have atTop : NativeBelow (indexedTerm A P U (bandImage S l j))
      (indexedTerm A P U (closedTower S (l+2))) :=
    let edge := NativeIndexedCarrierChecks.exact_IndexedCarrier S A P.val U.val
      (closedTower S (l+2)).val P.property U.property (closedTower S (l+2)).property
    (edge.2 (bandImage S l j).val (bandImage S l j).property indexBelow).1
  exact laws.backward atTop (approached j j (Or.inl rfl))

/-- The same conditional realization result, now for the *actual applied*
original iterator with the original closed native index argument, rather
than just for a carrier that has already reduced. -/
theorem exact_OriginalTowerBandFullPrefixIteratorRealization (S : Signature) (l : Nat) (A : SemanticType)
    (P : ClosedNativeTerm S (functionType A)) (U : ClosedNativeTerm S (actualType A))
    {f : V → V} {x : V} {orbit : BandCoords → V}
    {realizes : ClosedNativeTerm S (actualType A) → V → Prop}
    (equations : FullPrefixEquations BandLex f x orbit)
    (laws : RealizationLaws BandLex (@NativeBelow S (actualType A)) (fun u => applyClosed P u) f realizes)
    (seedValue : realizes U x) :
    (∀ i j, (j = i ∨ BandLex j i) → realizes (appliedIterator A (bandImage S l i) P U) (orbit j)) ∧
    (∀ j, realizes (appliedIterator A (closedTower S (l+2)) P U) (orbit j)) := by
  have carrier := exact_OriginalTowerBandFullPrefixCarrierRealization S l A P U equations laws seedValue
  refine ⟨?_,?_⟩
  · intro i j earlier
    exact laws.backward (exact_CanonicalAppliedIteratorAboveIndexed A (bandImage S l i) P U)
      (carrier.1 i j earlier)
  · intro j
    exact laws.backward (exact_CanonicalAppliedIteratorAboveIndexed A (closedTower S (l+2)) P U)
      (carrier.2 j)

#print axioms exact_OriginalTowerBandFullPrefixCarrierRealization
#print axioms exact_OriginalTowerBandFullPrefixIteratorRealization

end LogicLineages.PersistentMarking.NativeTowerBandFullPrefixIterationProof
