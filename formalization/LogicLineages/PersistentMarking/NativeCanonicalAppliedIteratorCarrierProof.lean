import LogicLineages.PersistentMarking.NativeIteratorStrictChecks
import LogicLineages.PersistentMarking.NativeIteratorChecks
import LogicLineages.PersistentMarking.NativeIndexedCarrierSubtype
import LogicLineages.PersistentMarking.StablePairProof

namespace LogicLineages.PersistentMarking.NativeCanonicalAppliedIteratorCarrierProof
open Spine NativeIndexedCarrierTargets NativeIteratorTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeIndexedCarrierSubtype

/-- The original iterator at its actual finite type, applied to the three
literal typed operands using the original application constructor. -/
def appliedIterator {S : Signature} (A : SemanticType) (i : ClosedNativeTerm S indexType)
    (P : ClosedNativeTerm S (functionType A)) (U : ClosedNativeTerm S (actualType A)) :
    ClosedNativeTerm S (actualType A) :=
  applyClosed (applyClosed (applyClosed
    ⟨iterator A,NativeIteratorChecks.exact_ClosedNativeIterator S A⟩ i) P) U

theorem exact_AppliedIteratorLiteral {S : Signature} (A : SemanticType)
    (i : ClosedNativeTerm S indexType) (P : ClosedNativeTerm S (functionType A))
    (U : ClosedNativeTerm S (actualType A)) :
    (appliedIterator A i P U).val = applied A i.val P.val U.val := rfl

/-- Canonical subtype endpoints for the three original strict beta steps. -/
theorem exact_CanonicalAppliedIteratorAboveIndexed {S : Signature} (A : SemanticType)
    (i : ClosedNativeTerm S indexType) (P : ClosedNativeTerm S (functionType A))
    (U : ClosedNativeTerm S (actualType A)) :
    NativeBelow (indexedTerm A P U i) (appliedIterator A i P U) := by
  obtain ⟨start,afterI,afterP,last,startRaw,_,_,lastRaw,first,second,third⟩ :=
    NativeIteratorStrictChecks.exact_IteratorNativeStrictChain S A i.val P.val U.val
      i.property P.property U.property
  have startEq : start = appliedIterator A i P U :=
    Subtype.ext (startRaw.trans (exact_AppliedIteratorLiteral A i P U).symm)
  have lastEq : last = indexedTerm A P U i := Subtype.ext lastRaw
  have two : NativeBelow afterP start :=
    StablePairProof.strictTransitive S start.val afterI.val afterP.val first second
  have all : NativeBelow last start :=
    StablePairProof.strictTransitive S start.val afterP.val last.val two third
  rw [startEq,lastEq] at all
  exact all

#print axioms exact_AppliedIteratorLiteral
#print axioms exact_CanonicalAppliedIteratorAboveIndexed

end LogicLineages.PersistentMarking.NativeCanonicalAppliedIteratorCarrierProof
