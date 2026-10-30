module

public import LogicLineages.ModelsAlgebra.Forests.LeafOrderTargets
public import LogicLineages.ModelsAlgebra.Forests.TwinRankProof
public import LogicLineages.ModelsAlgebra.Forests.LeafClusterProof

/-! Descendant-leaf clusters recover the actual order once equal-cluster
chains are ranked. This is proved from foresthood and finite maximal extension. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.LeafOrderProof

open GraphBridge TwinRankProof

theorem mem_finiteLeafCluster (F : FiniteOrderForest) (x : F.Carrier) (ℓ : ForestLeaf F) :
    ℓ ∈ finiteLeafCluster F x ↔ x ≤ ℓ.val := by
  classical
  simp [finiteLeafCluster]

theorem vertexLeafClusterNonempty : Targets.VertexLeafClusterNonempty := by
  intro F x
  obtain ⟨y, hxy, hy⟩ := exists_leaf_above x
  exact ⟨⟨y, hy⟩, (mem_finiteLeafCluster F x ⟨y, hy⟩).mpr hxy⟩

theorem orderReversesLeafClusterInclusion : Targets.OrderReversesLeafClusterInclusion := by
  intro F x y hxy ℓ hℓ
  exact (mem_finiteLeafCluster F x ℓ).mpr (le_trans hxy ((mem_finiteLeafCluster F y ℓ).mp hℓ))

private theorem neighborhood_subset_of_equal_clusters (F : FiniteOrderForest) (x y : F.Carrier)
    (hxy : x ≤ y) (heq : finiteLeafCluster F x = finiteLeafCluster F y) :
    closedNeighborhood (comparabilityGraph F) x ⊆ closedNeighborhood (comparabilityGraph F) y := by
  intro z hz
  apply (mem_closed_iff F y z).mpr
  rcases (mem_closed_iff F x z).mp hz with hxz | hzx
  · obtain ⟨ℓ, hzℓ, hmax⟩ := exists_leaf_above z
    have hxℓ : (⟨ℓ, hmax⟩ : ForestLeaf F) ∈ finiteLeafCluster F x :=
      (mem_finiteLeafCluster F x ⟨ℓ, hmax⟩).mpr (le_trans hxz hzℓ)
    rw [heq] at hxℓ
    exact F.forest ((mem_finiteLeafCluster F y ⟨ℓ, hmax⟩).mp hxℓ) hzℓ
  · exact Or.inr (le_trans hzx hxy)

theorem leafClusterEqualityIffNeighborhoodEquality : Targets.LeafClusterEqualityIffNeighborhoodEquality := by
  intro F x y
  constructor
  · intro heq
    obtain ⟨ℓ, hxℓ⟩ := vertexLeafClusterNonempty F x
    have hyℓ : ℓ ∈ finiteLeafCluster F y := heq ▸ hxℓ
    rcases F.forest ((mem_finiteLeafCluster F x ℓ).mp hxℓ)
        ((mem_finiteLeafCluster F y ℓ).mp hyℓ) with hxy | hyx
    · exact Set.Subset.antisymm (neighborhood_subset_of_equal_clusters F x y hxy heq)
        (orderReversesNeighborhoodInclusion F x y hxy)
    · exact (Set.Subset.antisymm (neighborhood_subset_of_equal_clusters F y x hyx heq.symm)
        (orderReversesNeighborhoodInclusion F y x hyx)).symm
  · intro heq
    have transfer (a b : F.Carrier)
        (hsub : closedNeighborhood (comparabilityGraph F) a ⊆
          closedNeighborhood (comparabilityGraph F) b) :
        finiteLeafCluster F a ⊆ finiteLeafCluster F b := by
      intro ℓ hℓ
      apply (mem_finiteLeafCluster F b ℓ).mpr
      have hn := hsub ((mem_closed_iff F a ℓ.val).mpr
        (Or.inl ((mem_finiteLeafCluster F a ℓ).mp hℓ)))
      rcases (mem_closed_iff F b ℓ.val).mp hn with h | h
      · exact h
      · exact ℓ.property h
    exact Finset.Subset.antisymm (transfer x y heq.subset) (transfer y x heq.symm.subset)

theorem leafClusterRankOrderRecovery : Targets.LeafClusterRankOrderRecovery := by
  intro F x y
  constructor
  · intro hxy
    exact ⟨orderReversesLeafClusterInclusion F x y hxy, fun heq =>
      (twinRankOrder F x y ((leafClusterEqualityIffNeighborhoodEquality F x y).mp heq)).mp hxy⟩
  · rintro ⟨hsub, hr⟩
    obtain ⟨ℓ, hyℓ⟩ := vertexLeafClusterNonempty F y
    rcases F.forest ((mem_finiteLeafCluster F x ℓ).mp (hsub hyℓ))
        ((mem_finiteLeafCluster F y ℓ).mp hyℓ) with hxy | hyx
    · exact hxy
    · have heq := Finset.Subset.antisymm (orderReversesLeafClusterInclusion F y x hyx) hsub
      exact (twinRankOrder F x y ((leafClusterEqualityIffNeighborhoodEquality F x y).mp heq)).mpr (hr heq)

theorem twinRankBelowCarrierCard : Targets.TwinRankBelowCarrierCard := by
  classical
  intro F x
  apply lt_of_lt_of_le (twinRankBound F x)
  simpa only [twinCard, Finset.card_univ] using
    (Finset.card_filter_le (Finset.univ : Finset F.Carrier) (fun y => y ∈ twinClass F x))

theorem actualLeafClusterFamilyLaminar : Targets.ActualLeafClusterFamilyLaminar := by
  classical
  intro F
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    exact vertexLeafClusterNonempty F v
  · intro a
    have ha : finiteLeafCluster F a.val = {a} := by
      ext ℓ
      rw [mem_finiteLeafCluster, Finset.mem_singleton]
      constructor
      · intro h
        exact Subtype.ext (le_antisymm (a.property h) h)
      · intro h; subst ℓ; exact le_rfl
    exact Finset.mem_image.mpr ⟨a.val, Finset.mem_univ _, ha⟩
  · intro B hB C hC
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
    rcases LeafClusterProof.leafClustersLaminar F v w with h | h | h
    · left
      intro ℓ hℓ
      exact (mem_finiteLeafCluster F w ℓ).mpr (h ((mem_finiteLeafCluster F v ℓ).mp hℓ))
    · right; left
      intro ℓ hℓ
      exact (mem_finiteLeafCluster F v ℓ).mpr (h ((mem_finiteLeafCluster F w ℓ).mp hℓ))
    · right; right
      apply Finset.disjoint_left.mpr
      intro ℓ hv hw
      exact Set.disjoint_left.mp h ((mem_finiteLeafCluster F v ℓ).mp hv)
        ((mem_finiteLeafCluster F w ℓ).mp hw)

end LogicLineages.ModelsAlgebra.Forests.LeafOrderProof
