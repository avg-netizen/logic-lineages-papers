module

public import LogicLineages.PersistentMarking.OrdinalNativeIterationTargets
public import LogicLineages.PersistentMarking.OrdinalRealizationClosureProof
public import LogicLineages.PersistentMarking.OrdinalRankSupportProof

public section

namespace LogicLineages.PersistentMarking.OrdinalIndexedCarrierOrbitProof
open OrdinalRealizationTargets OrdinalNativeIterationTargets
open OrdinalRealizationClosureProof OrdinalRankSupportProof

theorem exact_IndexedCarrierRealizesOrbit (terms : TermStructure)
    (wf : WellFounded (terms.below .base)) (appEdge : StrictFunctionSlot terms)
    (W : IndexedCarrier terms) (edges : IndexedCarrierEdges terms W) :
    IndexedCarrierRealizesOrbit terms wf W := by
  intro A f x orbit equations P U i hP hU β bound
  have backwards := exact_RealizationStrictBackward terms wf appEdge A
  have family := exact_RealizationCountableSupremum terms wf A
  have allStages (i : terms.term .base) (access : Acc (terms.below .base) i) :
      ∀ (stage : Ordinal.{0}) (count : Countable {γ : Ordinal.{0} // γ < stage}),
        stage ≤ access.rank → Realizes terms wf A (W A P U i) (orbit ⟨stage, count⟩) := by
    induction access with
    | intro i children outer =>
      intro stage
      induction stage using Ordinal.limitRecOn with
      | zero =>
        intro count _
        rw [equations.1 ⟨0, count⟩ rfl]
        exact backwards (W A P U i) U x (edges A P U i).1 hU
      | add_one γ inner =>
        intro count bound
        have successorBound : Order.succ γ ≤ (Acc.intro i children).rank := by
          simpa only [Order.succ_eq_add_one] using bound
        obtain ⟨j, edge, lowerBound⟩ :=
          exact_RankImmediateSuccessor (Acc.intro i children) γ successorBound
        let current : CountableOrdinal := ⟨γ + 1, count⟩
        let previous := earlierStage current ⟨γ, Order.lt_add_one_iff.mpr le_rfl⟩
        have previousRealizes : Realizes terms wf A (W A P U j) (orbit previous) :=
          outer j edge γ previous.property lowerBound
        have afterFunction : Realizes terms wf A (terms.app A A P (W A P U j)) (f (orbit previous)) :=
          hP (orbit previous) (W A P U j) previousRealizes
        rw [equations.2.1 previous current rfl]
        exact backwards (W A P U i) (terms.app A A P (W A P U j)) (f (orbit previous))
          ((edges A P U i).2 j edge).2 afterFunction
      | limit current isLimit inner =>
        intro count bound
        let stage : CountableOrdinal := ⟨current, count⟩
        letI : Countable (EarlierStages stage) := count
        letI : Nonempty (EarlierStages stage) := ⟨⟨0, isLimit.pos⟩⟩
        apply family (EarlierStages stage) (W A P U i)
          (fun η => orbit (earlierStage stage η)) (orbit stage) (equations.2.2 stage isLimit)
        intro η
        exact inner η.val η.property (earlierStage stage η).property (η.property.le.trans bound)
  exact allStages i (wf.apply i) β.val β.property bound

#print axioms exact_IndexedCarrierRealizesOrbit

end LogicLineages.PersistentMarking.OrdinalIndexedCarrierOrbitProof
