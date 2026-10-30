module

public import LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelTargets
public import LogicLineages.ModelsAlgebra.Forests.SmallTemplateProof
public import LogicLineages.ModelsAlgebra.Forests.LeafOrderProof

/-! Transport all actual descendant-leaf clusters into the finite small-template
supplier, preserving actual injective leaf labels rather than assuming them. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof

theorem laminarLeafEquivRelabeling : Targets.LaminarLeafEquivRelabeling := by
  classical
  intro α β family e h
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.map_nonempty.mpr (h.1 C hC)
  · intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact Finset.mem_image.mpr ⟨{a}, h.2.1 a, Finset.map_singleton e.toEmbedding a⟩
  · intro B hB C hC
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
    rcases h.2.2 B₀ hB₀ C₀ hC₀ with h | h | h
    · exact Or.inl (Finset.map_subset_map.mpr h)
    · exact Or.inr (Or.inl (Finset.map_subset_map.mpr h))
    · exact Or.inr (Or.inr ((Finset.disjoint_map e.toEmbedding).mpr h))

theorem smallForestLeafLabeling : Targets.SmallForestLeafLabeling := by
  classical
  intro F m hm hw
  let n := Fintype.card (ForestLeaf F)
  have hn : n ≤ m := by
    have hcard := (widthAtMost_iff_leaf_card F.forest m).mp hw
    simpa only [n, Fintype.card_subtype, leafFinset] using hcard
  let en : ForestLeaf F ≃ Fin n := Fintype.equivFin (ForestLeaf F)
  let family : Finset (Finset (Fin n)) :=
    (leafClusterFamily F).image (fun B => B.map en.toEmbedding)
  have hlam : IsLaminarLeafFamily family := by
    convert laminarLeafEquivRelabeling (ForestLeaf F) (Fin n) (leafClusterFamily F) en
      (LeafOrderProof.actualLeafClusterFamilyLaminar F) using 1 <;>
      ext B <;> simp only [family, Finset.mem_image]
  obtain ⟨f, hf, hfamily⟩ := SmallTemplateProof.smallLaminarCombLabeling
    ⟨m, by omega⟩ ⟨n, by omega⟩ hn family hlam
  let e : ForestLeaf F ↪ Fin m := en.toEmbedding.trans ⟨f, hf⟩
  refine ⟨e, fun v => ?_⟩
  have hsource : finiteLeafCluster F v ∈ leafClusterFamily F :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hencoded : (finiteLeafCluster F v).map en.toEmbedding ∈ family :=
    Finset.mem_image.mpr ⟨finiteLeafCluster F v, hsource, rfl⟩
  have h := hfamily _ hencoded
  have heq : ((finiteLeafCluster F v).map en.toEmbedding).image f =
      (finiteLeafCluster F v).map e := by
    calc
      _ = ((finiteLeafCluster F v).map en.toEmbedding).map (⟨f, hf⟩ : Fin n ↪ Fin m) :=
        (Finset.map_eq_image (⟨f, hf⟩ : Fin n ↪ Fin m) _).symm
      _ = _ := Finset.map_map _ _ _
  exact heq ▸ h

end LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof
