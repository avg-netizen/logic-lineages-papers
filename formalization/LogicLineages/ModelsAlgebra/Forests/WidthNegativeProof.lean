module

public import LogicLineages.ModelsAlgebra.Forests.WidthNegativeTargets
public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof
public import LogicLineages.ModelsAlgebra.Forests.SplitForestProof

/-! The complete m≥4 obstruction for actual finite order-forest JEP.
Cluster preservation is derived from saturation, not imposed on embeddings. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof

theorem clusterCommonHostObstruction : Targets.ClusterCommonHostObstruction := by
  classical
  intro F G hF hcard hnest hbad
  rintro ⟨H, hwidth, ⟨eF⟩, ⟨eG⟩⟩
  have hHF : (leafFinset H.Carrier).card ≤ (leafFinset F.Carrier).card :=
    (widthAtMost_iff_leaf_card H.forest _).mp hwidth
  have hHG : (leafFinset H.Carrier).card ≤ (leafFinset G.Carrier).card := hcard ▸ hHF
  obtain ⟨bF, _, hcomplete⟩ := ClusterCompletenessProof.saturatedHostClusterComplete F H eF hF hHF
  obtain ⟨bG, _, htransport⟩ := LeafClusterProof.saturatedClusterTransport G H eG hHG
  let p : ForestLeaf G ≃ ForestLeaf F := bG.trans bF.symm
  have hmap (w : G.Carrier) (v : F.Carrier)
      (hv : ∀ ℓ : ForestLeaf F, eG w ≤ (bF ℓ).val ↔ v ≤ ℓ.val) :
      finiteLeafCluster F v = (finiteLeafCluster G w).map p.toEmbedding := by
    ext ℓ
    obtain ⟨a, rfl⟩ := p.surjective ℓ
    simp only [finiteLeafCluster, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map_equiv, Equiv.symm_apply_apply]
    have ht : eG w ≤ (bF (p a)).val ↔ w ≤ a.val := by
      simpa only [p, Equiv.trans_apply, Equiv.apply_symm_apply, leafCluster, Set.mem_setOf_eq]
        using htransport w a
    exact (hv (p a)).symm.trans ht
  obtain ⟨u, v, hdis, hu, hv⟩ := hbad
  obtain ⟨uF, huF⟩ := hcomplete (eG u)
  obtain ⟨vF, hvF⟩ := hcomplete (eG v)
  have hequ := hmap u uF huF
  have heqv := hmap v vF hvF
  have huFc : 2 ≤ (finiteLeafCluster F uF).card := by
    rw [hequ, Finset.card_map]; exact hu
  have hvFc : 2 ≤ (finiteLeafCluster F vF).card := by
    rw [heqv, Finset.card_map]; exact hv
  have hdisF : Disjoint (finiteLeafCluster F uF) (finiteLeafCluster F vF) := by
    rw [hequ, heqv]
    exact (Finset.disjoint_map p.toEmbedding).mpr hdis
  rcases hnest uF vF huFc hvFc with hsub | hsub
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (finiteLeafCluster F uF).card)
    exact Finset.disjoint_left.mp hdisF ha (hsub ha)
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (finiteLeafCluster F vF).card)
    exact Finset.disjoint_left.mp hdisF (hsub ha) ha

theorem widthAtLeastFourFailsJEP : Targets.WidthAtLeastFourFailsJEP := by
  intro m hm hj
  obtain ⟨F, hF, hFc, hnest⟩ := CombForestProof.actualCombForest m (by omega)
  obtain ⟨G, hGc, hbad⟩ := SplitForestProof.actualSplitForest m hm
  have hFw : WidthAtMost F.Carrier m := (widthAtMost_iff_leaf_card F.forest m).mpr hFc.le
  have hGw : WidthAtMost G.Carrier m := (widthAtMost_iff_leaf_card G.forest m).mpr hGc.le
  obtain ⟨H, hHw, heF, heG⟩ := hj F G hFw hGw
  apply clusterCommonHostObstruction F G hF (hFc.trans hGc.symm) hnest hbad
  exact ⟨H, by simpa only [hFc] using hHw, heF, heG⟩

end LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof
