module

public import LogicLineages.NativeModule.PersistentMarking.NativeClosedApplication
public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedTypingThinProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype
open NativeIndexedCarrierTargets NativeIteratorStrictTargets

/-- The original indexed carrier at its actual closed native result type. -/
def indexedTerm {S} (A : SemanticType)
    (P : ClosedNativeTerm S (.arrow (actualType A) (actualType A)))
    (U : ClosedNativeTerm S (actualType A)) (i : ClosedNativeTerm S indexType) :
    ClosedNativeTerm S (actualType A) :=
  ⟨indexedW A P.val U.val i.val,
    NativeIndexedTypingThinProof.indexedClosed S A P.val U.val i.val P.property U.property i.property⟩

end LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype
