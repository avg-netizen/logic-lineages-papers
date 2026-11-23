module

public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedCarrierSubtypeTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedCarrierChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierSubtypeChecks
open NativeIndexedCarrierTargets NativeIndexedCarrierSubtypeTargets

theorem exact_IndexedCarrierSubtypeEdges : IndexedCarrierSubtypeEdges := by
  intro S A P U i
  obtain ⟨base, steps⟩ := NativeIndexedCarrierChecks.exact_IndexedCarrier S A P.val U.val i.val
    P.property U.property i.property
  refine ⟨rfl, ?_, ?_⟩
  · change ConfinedPair.Strict S (indexedW A P.val U.val i.val) U.val
    exact base
  · intro j edge
    change ConfinedPair.Strict S i.val j.val at edge
    change ConfinedPair.Strict S (indexedW A P.val U.val i.val) (indexedW A P.val U.val j.val) ∧
      ConfinedPair.Strict S (indexedW A P.val U.val i.val)
        (NativeReduction.app (actualType A) (actualType A) P.val (indexedW A P.val U.val j.val))
    exact steps j.val j.property edge

#print axioms exact_IndexedCarrierSubtypeEdges

end LogicLineages.PersistentMarking.NativeIndexedCarrierSubtypeChecks
