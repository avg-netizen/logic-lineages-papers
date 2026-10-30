module

public import LogicLineages.ModelsAlgebra.Forests.CanonicalOrderTargets
public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalProof

/-! Constructing actual finite order forests from induced-P4/C4-free graphs.
Equal closed neighborhoods are linearly ordered by finite rank; strict reverse
inclusion fixes all other comparisons. No representation supplier is assumed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CanonicalOrderProof

open GraphBridge

private theorem rank_injective {α : Type} [Fintype α] :
    Function.Injective (canonicalRank (α := α)) := by
  intro x y h
  apply (Fintype.equivFin α).injective
  exact Fin.ext h

theorem canonicalPartialOrderLaws : Targets.CanonicalPartialOrderLaws := by
  intro α _ G
  refine ⟨fun x => ⟨Set.Subset.refl _, fun _ => le_rfl⟩, ?_, ?_⟩
  · intro x y z hxy hyz
    refine ⟨hyz.1.trans hxy.1, fun h => ?_⟩
    have hxy_eq : closedNeighborhood G x = closedNeighborhood G y :=
      Set.Subset.antisymm (by rw [h]; exact hyz.1) hxy.1
    have hyz_eq : closedNeighborhood G y = closedNeighborhood G z := hxy_eq.symm.trans h
    exact le_trans (hxy.2 hxy_eq) (hyz.2 hyz_eq)
  · intro x y hxy hyx
    have h : closedNeighborhood G x = closedNeighborhood G y :=
      Set.Subset.antisymm hyx.1 hxy.1
    exact rank_injective (le_antisymm (hxy.2 h) (hyx.2 h.symm))

private theorem nested_comparable {α : Type} [Fintype α] (G : SimpleGraph α) (x y : α)
    (h : closedNeighborhood G x ⊆ closedNeighborhood G y ∨
      closedNeighborhood G y ⊆ closedNeighborhood G x) :
    canonicalLE G x y ∨ canonicalLE G y x := by
  classical
  by_cases heq : closedNeighborhood G x = closedNeighborhood G y
  · rcases le_total (canonicalRank x) (canonicalRank y) with hr | hr
    · exact Or.inl ⟨heq.symm.subset, fun _ => hr⟩
    · exact Or.inr ⟨heq.subset, fun _ => hr⟩
  · rcases h with h | h
    · exact Or.inr ⟨h, fun he => False.elim (heq he.symm)⟩
    · exact Or.inl ⟨h, fun he => False.elim (heq he)⟩

theorem canonicalAdjacencyComparability : Targets.CanonicalAdjacencyComparability := by
  intro α _ G hp hc x y
  constructor
  · intro hxy
    exact ⟨G.ne_of_adj hxy, nested_comparable G x y
      (GraphUniversalProof.adjacentClosedNeighborhoodsNested α G hp hc x y hxy)⟩
  · rintro ⟨hne, h | h⟩
    · exact (h.1 (Or.inl rfl)).resolve_left hne.symm
    · exact G.adj_symm ((h.1 (Or.inl rfl)).resolve_left hne)

theorem canonicalPredecessorsChain : Targets.CanonicalPredecessorsChain := by
  classical
  intro α _ G hp hc x y z hx hy
  have hxz : x ∈ closedNeighborhood G z := by
    rcases hx.1 (Or.inl rfl) with heq | hadj
    · exact Or.inl heq.symm
    · exact Or.inr (G.adj_symm hadj)
  rcases hy.1 hxz with heq | hadj
  · subst y
    exact Or.inl ((canonicalPartialOrderLaws α G).1 x)
  · exact ((canonicalAdjacencyComparability α G hp hc x y).mp (G.adj_symm hadj)).2

theorem canonicalGraphRepresentation : Targets.CanonicalGraphRepresentation := by
  intro α inst G hp hc
  let po : PartialOrder α := {
    le := canonicalLE G
    le_refl := (canonicalPartialOrderLaws α G).1
    le_trans := (canonicalPartialOrderLaws α G).2.1
    le_antisymm := (canonicalPartialOrderLaws α G).2.2 }
  let F : FiniteOrderForest := {
    Carrier := α
    carrierFintype := inst
    carrierPartialOrder := po
    forest := fun {x y z} hx hy => canonicalPredecessorsChain α G hp hc x y z hx hy }
  refine ⟨F, ⟨⟨Equiv.refl α, ?_⟩⟩⟩
  intro x y
  change (x ≠ y ∧ (canonicalLE G x y ∨ canonicalLE G y x)) ↔ G.Adj x y
  exact (canonicalAdjacencyComparability α G hp hc x y).symm

end LogicLineages.ModelsAlgebra.Forests.CanonicalOrderProof
