module

public import LogicLineages.PersistentMarking.OrdinalRealizationTargets

public section

namespace LogicLineages.PersistentMarking.OrdinalRealizationClosureProof
open OrdinalRealizationTargets

private theorem countableSup (ι : Type 1) [Countable ι] (f : ι → CountableOrdinal) :
    Countable {β : Ordinal.{0} // β < ⨆ i, (f i).val} := by
  have cover : Set.Iio (⨆ i, (f i).val) = ⋃ i, Set.Iio (f i).val := by
    ext β
    simp only [Set.mem_Iio, Set.mem_iUnion, Ordinal.lt_iSup_iff]
  change (Set.Iio (⨆ i, (f i).val)).Countable
  rw [cover]
  exact Set.countable_iUnion (fun i => (f i).property)

theorem exact_PointwiseSupremumExists : PointwiseSupremumExists := by
  intro A
  induction A with
  | base =>
    intro ι hCount hNonempty f
    letI : Countable ι := hCount
    let sup : CountableOrdinal := ⟨⨆ i, (f i).val, countableSup ι f⟩
    refine ⟨sup, rfl, ?_⟩
    intro v hv
    exact Subtype.ext hv
  | arrow A D _ ih =>
    intro ι hCount hNonempty f
    have point (x : Value A) : ∃! v, PointwiseSupremum D (fun i => f i x) v :=
      @ih ι hCount hNonempty (fun i => f i x)
    classical
    let sup : Value A → Value D := fun x => Classical.choose (point x).exists
    have atPoint (x : Value A) : PointwiseSupremum D (fun i => f i x) (sup x) :=
      Classical.choose_spec (point x).exists
    refine ⟨sup, atPoint, ?_⟩
    intro g hg
    funext x
    exact (point x).unique (hg x) (atPoint x)

theorem exact_RealizationStrictBackward (terms : TermStructure) (wf : WellFounded (terms.below .base))
    (liftEdge : StrictFunctionSlot terms) : RealizationStrictBackward terms wf := by
  intro A
  induction A with
  | base =>
    intro s t v edge ht
    have rankDrop : (wf.apply t).rank < (wf.apply s).rank :=
      (wf.apply s).rank_lt_of_rel edge
    exact (show v.val ≤ (wf.apply t).rank from ht).trans rankDrop.le
  | arrow A D _ ih =>
    intro s t f edge ht x u hu
    exact ih (terms.app A D s u) (terms.app A D t u) (f x)
      (liftEdge A D s t u edge) (ht x u hu)

theorem exact_RealizationDownward (terms : TermStructure) (wf : WellFounded (terms.below .base)) :
    RealizationDownward terms wf := by
  intro A
  induction A with
  | base =>
    intro t v w hl hw
    exact (show v.val ≤ w.val from hl).trans (show w.val ≤ (wf.apply t).rank from hw)
  | arrow A D _ ih =>
    intro t f g hl hg x u hu
    exact ih (terms.app A D t u) (f x) (g x) (hl x) (hg x u hu)

theorem exact_RealizationCountableSupremum (terms : TermStructure)
    (wf : WellFounded (terms.below .base)) : RealizationCountableSupremum terms wf := by
  intro A
  induction A with
  | base =>
    intro ι hCount hNonempty t f v hv hFamily
    letI : Countable ι := hCount
    change v.val ≤ (wf.apply t).rank
    change v.val = ⨆ i, (f i).val at hv
    rw [hv]
    exact Ordinal.iSup_le_iff.mpr fun i => hFamily i
  | arrow A D _ ih =>
    intro ι hCount hNonempty t f g hg hFamily x u hu
    exact @ih ι hCount hNonempty (terms.app A D t u) (fun i => f i x) (g x)
      (hg x) (fun i => hFamily i x u hu)

#print axioms exact_PointwiseSupremumExists
#print axioms exact_RealizationStrictBackward
#print axioms exact_RealizationDownward
#print axioms exact_RealizationCountableSupremum

end LogicLineages.PersistentMarking.OrdinalRealizationClosureProof
