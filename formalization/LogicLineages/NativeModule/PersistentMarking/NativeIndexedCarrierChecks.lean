module

public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedSelectorProof
public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedContextThinProof
public import LogicLineages.NativeModule.PersistentMarking.NativeCarrierThinChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierChecks
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIndexedTypingThinProof

theorem exact_IndexedCarrier : IndexedCarrier := by
  intro S A P U i hP hU hi
  have hK := kClosed S A P i hP hi
  have hSelect := NativeIndexedSelectorProof.selectP S A P i hP hi
  have hWeak := ElementaryProof.strictIncluded S (K A P i) P hSelect.2.1
  have hCarrier := NativeCarrierThinChecks.exact_Carrier S (actualType A) P (K A P i) U
    hP hK hU hWeak hSelect.2.2
  refine ⟨hCarrier.1,?_⟩
  intro j hj h
  have hIndex := NativeIndexedContextThinProof.contextStrict S A P U i j hP hU hi hj h
  exact ⟨hIndex,hCarrier.2 (indexedW A P U j) (indexedClosed S A P U j hP hU hj).1 hIndex.2.2 hIndex⟩

#print axioms exact_IndexedCarrier

end LogicLineages.PersistentMarking.NativeIndexedCarrierChecks
