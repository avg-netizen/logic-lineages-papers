module

public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedCarrierSubtype

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierSubtypeTargets
open NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeIndexedCarrierSubtype

def IndexedCarrierSubtypeEdges : Prop :=
  ∀ S A
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType),
    (indexedTerm A P U i).val = indexedW A P.val U.val i.val ∧
    NativeBelow U (indexedTerm A P U i) ∧
    ∀ j : ClosedNativeTerm S indexType, NativeBelow j i →
      NativeBelow (indexedTerm A P U j) (indexedTerm A P U i) ∧
      NativeBelow (applyClosed P (indexedTerm A P U j)) (indexedTerm A P U i)

end LogicLineages.PersistentMarking.NativeIndexedCarrierSubtypeTargets
