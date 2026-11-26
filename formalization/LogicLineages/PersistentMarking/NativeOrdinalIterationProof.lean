import LogicLineages.PersistentMarking.NativeOrdinalIterationTargets
import LogicLineages.PersistentMarking.NativeOrdinalRealizationProof
import LogicLineages.PersistentMarking.NativeIndexedCarrierSubtypeChecks
import LogicLineages.PersistentMarking.NativeIteratorStrictChecks
import LogicLineages.PersistentMarking.OrdinalNativeOrbitProof
import LogicLineages.PersistentMarking.OrdinalIndexedCarrierOrbitProof

namespace LogicLineages.PersistentMarking.NativeOrdinalIterationProof
open Spine NativeIndexedCarrierTargets NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalRealizationTargets NativeOrdinalRealizationProof NativeOrdinalIterationTargets
open NativeIndexedCarrierSubtype OrdinalRealizationTargets OrdinalRealizationClosureProof
open OrdinalNativeIterationTargets OrdinalNativeOrbitProof OrdinalIndexedCarrierOrbitProof

private def carrier (S : Signature) : OrdinalNativeIterationTargets.IndexedCarrier (nativeTerms S) :=
  fun A => indexedTerm (nativeShape A)

private theorem carrierEdges (S : Signature) : IndexedCarrierEdges (nativeTerms S) (carrier S) := by
  intro A P U i
  exact (NativeIndexedCarrierSubtypeChecks.exact_IndexedCarrierSubtypeEdges S (nativeShape A) P U i).2

theorem exact_NativeIndexedCarrierOrbit : NativeIndexedCarrierOrbit := by
  intro S
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  exact ⟨wf, exact_IndexedCarrierRealizesOrbit (nativeTerms S) wf (applicationEdge S)
    (carrier S) (carrierEdges S)⟩

theorem exact_NativeIteratorRealizesFullPrefix : NativeIteratorRealizesFullPrefix := by
  intro S
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  refine ⟨wf, ?_⟩
  intro A
  let iterate : Value (iteratorShape A) := fun α f x => orbit A f x α
  refine ⟨iterate, fun f x => orbitEquations A f x, ?_⟩
  intro α i hi f P hp x U hu
  let W := indexedTerm (nativeShape A) P U i
  have bound : α.val ≤ (wf.apply i).rank := hi
  have hW : Realizes (nativeTerms S) wf A W (orbit A f x α) :=
    exact_IndexedCarrierRealizesOrbit (nativeTerms S) wf (applicationEdge S) (carrier S)
      (carrierEdges S) A f x (orbit A f x) (orbitEquations A f x) P U i hp hu α bound
  obtain ⟨start, afterI, afterP, final, startValue, _, _, finalValue, edgeI, edgeP, edgeU⟩ :=
    NativeIteratorStrictChecks.exact_IteratorNativeStrictChain S (nativeShape A) i.val P.val U.val
      i.property P.property U.property
  let application := applyClosed (applyClosed (applyClosed (typedIterator S A) i) P) U
  have indexApplied : start = application := Subtype.ext startValue
  have finalIsW : final = W := Subtype.ext finalValue
  have backwards := exact_RealizationStrictBackward (nativeTerms S) wf (applicationEdge S) A
  have last : Realizes (nativeTerms S) wf A final (orbit A f x α) := by
    rw [finalIsW]
    exact hW
  have penultimate := backwards afterP final (orbit A f x α) edgeU last
  have intermediate := backwards afterI afterP (orbit A f x α) edgeP penultimate
  have initial := backwards start afterI (orbit A f x α) edgeI intermediate
  rw [indexApplied] at initial
  exact initial

#print axioms exact_NativeIndexedCarrierOrbit
#print axioms exact_NativeIteratorRealizesFullPrefix

end LogicLineages.PersistentMarking.NativeOrdinalIterationProof
