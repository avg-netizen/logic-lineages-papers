module

public import LogicLineages.ModelsAlgebra.Forests.TwinIsoTargets
public import LogicLineages.ModelsAlgebra.Forests.TwinRankProof

/-! Matching finite ranks in actual graph-twin classes reconstructs the forest
order up to isomorphism. The given graph map need not preserve order. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.TwinIsoProof

open GraphBridge
open TwinRankProof

theorem twinRankSurjective : Targets.TwinRankSurjective := by
  classical
  intro F x k hk
  let T : Finset F.Carrier := Finset.univ.filter (fun y => y ∈ twinClass F x)
  have hclass (y : T) : closedNeighborhood (comparabilityGraph F) y =
      closedNeighborhood (comparabilityGraph F) x := (Finset.mem_filter.mp y.property).2
  let r : T → Fin T.card := fun y => ⟨twinRank F y, by
    have hb := twinRankBound F y
    simpa only [twinCard, twinClass, Set.mem_setOf_eq, hclass y, T] using hb⟩
  have hinj : Function.Injective r := by
    intro a b hab
    have hr : twinRank F a = twinRank F b := congrArg Fin.val hab
    have heq := (hclass a).trans (hclass b).symm
    apply Subtype.ext
    exact le_antisymm ((twinRankOrder F a b heq).mpr (le_of_eq hr))
      ((twinRankOrder F b a heq.symm).mpr (le_of_eq hr.symm))
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).mpr ⟨hinj, by simp⟩
  obtain ⟨y, hy⟩ := hbij.surjective ⟨k, hk⟩
  have hyr : twinRank F y = k := congrArg Fin.val hy
  refine ⟨y, ⟨hclass y, hyr⟩, ?_⟩
  intro z hz
  have heq := hz.1.trans (hclass y).symm
  have hr : twinRank F z = twinRank F y := hz.2.trans hyr.symm
  exact le_antisymm ((twinRankOrder F z y heq).mpr (le_of_eq hr))
    ((twinRankOrder F y z heq.symm).mpr (le_of_eq hr.symm))

private theorem graphIso_mem (F G : FiniteOrderForest)
    (e : comparabilityGraph F ≃g comparabilityGraph G) (x z : F.Carrier) :
    e z ∈ closedNeighborhood (comparabilityGraph G) (e x) ↔
      z ∈ closedNeighborhood (comparabilityGraph F) x := by
  constructor
  · rintro (heq | hadj)
    · exact Or.inl (e.injective heq)
    · exact Or.inr (e.map_rel_iff.mp hadj)
  · rintro (heq | hadj)
    · exact Or.inl (congrArg e heq)
    · exact Or.inr (e.map_rel_iff.mpr hadj)

theorem graphIsoNeighborhoodSubset : Targets.GraphIsoNeighborhoodSubset := by
  intro F G e x y
  constructor
  · intro h z hz
    exact (graphIso_mem F G e y z).mp (h ((graphIso_mem F G e x z).mpr hz))
  · intro h z hz
    obtain ⟨a, rfl⟩ := e.surjective z
    exact (graphIso_mem F G e y a).mpr (h ((graphIso_mem F G e x a).mp hz))

theorem graphIsoNeighborhoodEquality : Targets.GraphIsoNeighborhoodEquality := by
  intro F G e x y
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((graphIsoNeighborhoodSubset F G e x y).mp h.subset)
      ((graphIsoNeighborhoodSubset F G e y x).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((graphIsoNeighborhoodSubset F G e x y).mpr h.subset)
      ((graphIsoNeighborhoodSubset F G e y x).mpr h.symm.subset)

theorem graphIsoTwinCard : Targets.GraphIsoTwinCard := by
  classical
  intro F G e x
  let t : {y // y ∈ twinClass F x} ≃ {z // z ∈ twinClass G (e x)} :=
    e.toEquiv.subtypeEquiv (fun y => (graphIsoNeighborhoodEquality F G e y x).symm)
  have h := Fintype.card_congr t
  simpa only [Fintype.card_subtype, twinCard] using h.symm

theorem rankMatchedOrderIso : Targets.RankMatchedOrderIso := by
  classical
  intro F G e
  have hex (x : F.Carrier) : ∃ y : G.Carrier,
      y ∈ twinClass G (e x) ∧ twinRank G y = twinRank F x := by
    have hb : twinRank F x < twinCard G (e x) := by
      rw [graphIsoTwinCard F G e x]
      exact twinRankBound F x
    exact (twinRankSurjective G (e x) (twinRank F x) hb).exists
  let f : F.Carrier → G.Carrier := fun x => Classical.choose (hex x)
  have hf (x : F.Carrier) :
      closedNeighborhood (comparabilityGraph G) (f x) =
          closedNeighborhood (comparabilityGraph G) (e x) ∧
        twinRank G (f x) = twinRank F x := Classical.choose_spec (hex x)
  have horder (x y : F.Carrier) : f x ≤ f y ↔ x ≤ y := by
    rw [twinRankOrderRecovery G (f x) (f y), twinRankOrderRecovery F x y]
    rw [(hf x).1, (hf y).1, (hf x).2, (hf y).2,
      graphIsoNeighborhoodSubset F G e y x, graphIsoNeighborhoodEquality F G e x y]
  have hinj : Function.Injective f := by
    intro x y hxy
    exact le_antisymm ((horder x y).mp (le_of_eq hxy))
      ((horder y x).mp (le_of_eq hxy.symm))
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, Fintype.card_congr e.toEquiv⟩
  let o : F.Carrier ≃o G.Carrier := {
    toEquiv := Equiv.ofBijective f hbij
    map_rel_iff' := fun {x y} => horder x y }
  exact ⟨o, hf⟩

theorem twinClassOrderUniqueness : Targets.TwinClassOrderUniqueness := by
  intro F G h
  obtain ⟨e⟩ := h
  obtain ⟨f, _⟩ := rankMatchedOrderIso F G e
  exact ⟨f⟩

end LogicLineages.ModelsAlgebra.Forests.TwinIsoProof
