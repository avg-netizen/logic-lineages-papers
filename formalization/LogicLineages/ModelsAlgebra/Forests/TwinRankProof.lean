module

public import LogicLineages.ModelsAlgebra.Forests.TwinRankTargets

/-! The actual forest order is recovered from its graph neighborhoods and
strict-predecessor ranks inside equal-neighborhood chains. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.TwinRankProof

open GraphBridge

theorem mem_closed_iff (F : FiniteOrderForest) (x z : F.Carrier) :
    z ∈ closedNeighborhood (comparabilityGraph F) x ↔ x ≤ z ∨ z ≤ x := by
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact Or.inl le_rfl
    · exact h
  · intro h
    by_cases heq : z = x
    · exact Or.inl heq
    · exact Or.inr ⟨Ne.symm heq, h⟩

theorem orderReversesNeighborhoodInclusion : Targets.OrderReversesNeighborhoodInclusion := by
  intro F x y hxy z hz
  apply (mem_closed_iff F x z).mpr
  rcases (mem_closed_iff F y z).mp hz with hyz | hzy
  · exact Or.inl (le_trans hxy hyz)
  · exact F.forest hxy hzy

theorem twinClassChain : Targets.TwinClassChain := by
  intro F x y h
  apply (mem_closed_iff F x y).mp
  rw [h]
  exact Or.inl rfl

private theorem rank_mono (F : FiniteOrderForest) (x y : F.Carrier)
    (heq : closedNeighborhood (comparabilityGraph F) x =
      closedNeighborhood (comparabilityGraph F) y) (hxy : x ≤ y) :
    twinRank F x ≤ twinRank F y := by
  classical
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, twinClass, Set.mem_setOf_eq] at hz ⊢
  exact ⟨hz.1.trans heq, lt_of_lt_of_le hz.2 hxy⟩

private theorem rank_strict (F : FiniteOrderForest) (x y : F.Carrier)
    (heq : closedNeighborhood (comparabilityGraph F) x =
      closedNeighborhood (comparabilityGraph F) y) (hxy : x < y) :
    twinRank F x < twinRank F y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, twinClass, Set.mem_setOf_eq] at hz ⊢
    exact ⟨hz.1.trans heq, lt_trans hz.2 hxy⟩
  · intro h
    have hx : x ∈ Finset.univ.filter (fun z => z ∈ twinClass F y ∧ z < y) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨heq, hxy⟩
    rw [← h] at hx
    exact (lt_irrefl x) (Finset.mem_filter.mp hx).2.2

theorem twinRankOrder : Targets.TwinRankOrder := by
  intro F x y heq
  constructor
  · exact rank_mono F x y heq
  · intro hr
    rcases twinClassChain F x y heq with hxy | hyx
    · exact hxy
    · by_contra hn
      have hlt : y < x := lt_of_le_not_ge hyx hn
      exact (not_lt_of_ge hr) (rank_strict F y x heq.symm hlt)

theorem twinRankOrderRecovery : Targets.TwinRankOrderRecovery := by
  intro F x y
  constructor
  · intro hxy
    exact ⟨orderReversesNeighborhoodInclusion F x y hxy,
      fun heq => (twinRankOrder F x y heq).mp hxy⟩
  · rintro ⟨hsub, hr⟩
    rcases (mem_closed_iff F x y).mp (hsub (Or.inl rfl)) with hxy | hyx
    · exact hxy
    · have heq := Set.Subset.antisymm
        (orderReversesNeighborhoodInclusion F y x hyx) hsub
      exact (twinRankOrder F x y heq).mpr (hr heq)

theorem twinRankBound : Targets.TwinRankBound := by
  classical
  intro F x
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.1⟩
  · intro heq
    have hx : x ∈ Finset.univ.filter (fun z => z ∈ twinClass F x) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
    rw [← heq] at hx
    exact (lt_irrefl x) (Finset.mem_filter.mp hx).2.2

end LogicLineages.ModelsAlgebra.Forests.TwinRankProof
