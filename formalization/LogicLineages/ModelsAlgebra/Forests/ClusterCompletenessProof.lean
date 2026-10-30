module

public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessTargets
public import LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof
public import LogicLineages.ModelsAlgebra.Forests.LeafClusterProof

/-! Maximal binary cluster families control all clusters in saturated hosts.
Host cluster nonemptiness is derived from finite maximal extension. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof

theorem finiteLeafClusterSemantics : Targets.FiniteLeafClusterSemantics := by
  classical
  intro F v ℓ
  simp [finiteLeafCluster, leafCluster]

theorem binaryForestClusterComplete : Targets.BinaryForestClusterComplete := by
  classical
  intro F hF A hA hcompat
  have hmem : A ∈ leafClusterFamily F :=
    BinaryClusterProof.binaryClusterFamilyMaximal (ForestLeaf F) Finset.univ
      (leafClusterFamily F) hF A hA (Finset.subset_univ A) (by
        intro B hB
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
        exact hcompat v)
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv⟩

theorem saturatedHostClusterComplete : Targets.SaturatedHostClusterComplete := by
  classical
  intro F H e hF hcard
  obtain ⟨b, hb, htransport⟩ := LeafClusterProof.saturatedClusterTransport F H e hcard
  refine ⟨b, hb, ?_⟩
  intro w
  let A : Finset (ForestLeaf F) := Finset.univ.filter (fun ℓ => w ≤ (b ℓ).val)
  have hAsem (ℓ : ForestLeaf F) : ℓ ∈ A ↔ w ≤ (b ℓ).val := by simp [A]
  have hA : A.Nonempty := by
    obtain ⟨z, hwz, hz⟩ := exists_leaf_above w
    obtain ⟨ℓ, hℓ⟩ := b.surjective ⟨z, hz⟩
    refine ⟨ℓ, (hAsem ℓ).mpr ?_⟩
    rw [hℓ]
    exact hwz
  have hcompat (v : F.Carrier) : ClusterCompatible A (finiteLeafCluster F v) := by
    rcases LeafClusterProof.leafClustersLaminar H w (e v) with hsub | hsub | hdis
    · left
      intro ℓ hℓ
      apply (finiteLeafClusterSemantics F v ℓ).mpr
      exact (htransport v ℓ).mp (hsub ((hAsem ℓ).mp hℓ))
    · right; left
      intro ℓ hℓ
      apply (hAsem ℓ).mpr
      exact hsub ((htransport v ℓ).mpr ((finiteLeafClusterSemantics F v ℓ).mp hℓ))
    · right; right
      apply Finset.disjoint_left.mpr
      intro ℓ hℓA hℓv
      exact Set.disjoint_left.mp hdis ((hAsem ℓ).mp hℓA)
        ((htransport v ℓ).mpr ((finiteLeafClusterSemantics F v ℓ).mp hℓv))
  obtain ⟨v, hv⟩ := binaryForestClusterComplete F hF A hA hcompat
  refine ⟨v, fun ℓ => ?_⟩
  simpa only [finiteLeafCluster, A, Finset.mem_filter, Finset.mem_univ, true_and]
    using (Finset.ext_iff.mp hv ℓ).symm

end LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof
