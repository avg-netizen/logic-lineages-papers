module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestTargets

/-! Literal laminar families realized by reverse-inclusion forests. Singleton
clusters are proved to be exactly the leaves; binary splits are transported,
not postulated, for the resulting forest. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.LaminarForestProof

theorem binaryClusterRelabeling : Targets.BinaryClusterRelabeling := by
  classical
  intro α β L family e h
  rcases h with ⟨hL, hnon, hsing, hlam, hsplit⟩
  refine ⟨Finset.mem_image.mpr ⟨L, hL, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨Finset.map_nonempty.mpr (hnon C hC).1,
      Finset.map_subset_map.mpr (hnon C hC).2⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_image.mpr ⟨{a}, hsing a ha, Finset.map_singleton e a⟩
  · intro B hB C hC
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
    rcases hlam B₀ hB₀ C₀ hC₀ with h | h | h
    · exact Or.inl (Finset.map_subset_map.mpr h)
    · exact Or.inr (Or.inl (Finset.map_subset_map.mpr h))
    · exact Or.inr (Or.inr ((Finset.disjoint_map e).mpr h))
  · intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    rcases hsplit B₀ hB₀ with h | ⟨C, hC, D, hD, hCn, hDn, hdis, hjoin⟩
    · left; simpa only [Finset.card_map] using h
    · right
      refine ⟨C.map e, Finset.mem_image.mpr ⟨C, hC, rfl⟩,
        D.map e, Finset.mem_image.mpr ⟨D, hD, rfl⟩,
        Finset.map_nonempty.mpr hCn, Finset.map_nonempty.mpr hDn,
        (Finset.disjoint_map e).mpr hdis, ?_⟩
      rw [← Finset.map_union, hjoin]

theorem laminarFamilyForestRepresentation : Targets.LaminarFamilyForestRepresentation := by
  classical
  intro α _ family h
  let F : FiniteOrderForest := {
    Carrier := OrderDual family
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := by
      intro x y z hx hy
      rcases h.2.2 x.val x.property y.val y.property with hxy | hyx | hdis
      · exact Or.inr hxy
      · exact Or.inl hyx
      · obtain ⟨a, ha⟩ := h.1 z.val z.property
        exact False.elim (Finset.disjoint_left.mp hdis (hx ha) (hy ha)) }
  let f : α → ForestLeaf F := fun a => ⟨⟨{a}, h.2.1 a⟩, by
    intro z hz
    change ({a} : Finset α) ⊆ z.val
    obtain ⟨c, hc⟩ := h.1 z.val z.property
    have hca : c = a := Finset.mem_singleton.mp (hz hc)
    exact Finset.singleton_subset_iff.mpr (hca ▸ hc)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hset : ({a} : Finset α) = {b} := congrArg (fun ℓ : ForestLeaf F => ℓ.val.val) hab
    exact Finset.singleton_inj.mp hset
  have hsurj : Function.Surjective f := by
    intro ℓ
    obtain ⟨a, ha⟩ := h.1 ℓ.val.val ℓ.val.property
    have hbelow : ℓ.val ≤ (⟨{a}, h.2.1 a⟩ : F.Carrier) := Finset.singleton_subset_iff.mpr ha
    have habove : ℓ.val.val ⊆ {a} := ℓ.property hbelow
    have heq : ℓ.val.val = {a} := Finset.Subset.antisymm habove hbelow
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact heq.symm
  let leaves : α ≃ ForestLeaf F := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨F, Equiv.refl family, leaves, ?_, ?_, ?_⟩
  · intro B C; rfl
  · intro B a
    exact Finset.singleton_subset_iff
  · intro a; rfl

theorem binaryFamilyForestRepresentation : Targets.BinaryFamilyForestRepresentation := by
  classical
  intro α _ family h
  have hlam : IsLaminarLeafFamily family :=
    ⟨fun B hB => (h.2.1 B hB).1, fun a => h.2.2.1 a (Finset.mem_univ a), h.2.2.2.1⟩
  obtain ⟨F, nodes, leaves, horder, hmem, hsing⟩ :=
    laminarFamilyForestRepresentation α family hlam
  have hcluster (B : family) : finiteLeafCluster F (nodes B) = B.val.map leaves.toEmbedding := by
    ext ℓ
    obtain ⟨a, rfl⟩ := leaves.surjective ℓ
    simpa only [finiteLeafCluster, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map_equiv, Equiv.symm_apply_apply] using hmem B a
  have hfamily : leafClusterFamily F = family.image (fun B => B.map leaves.toEmbedding) := by
    ext C
    constructor
    · intro hC
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨B, rfl⟩ := nodes.surjective v
      exact Finset.mem_image.mpr ⟨B.val, B.property, (hcluster B).symm⟩
    · intro hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
      exact Finset.mem_image.mpr ⟨nodes ⟨B, hB⟩, Finset.mem_univ _, hcluster ⟨B, hB⟩⟩
  refine ⟨F, nodes, leaves, horder, hmem, hsing, ?_⟩
  have hb := binaryClusterRelabeling α (ForestLeaf F) Finset.univ family leaves.toEmbedding h
  change IsBinaryClusterFamily Finset.univ (leafClusterFamily F)
  rw [hfamily]
  rw [Finset.map_univ_equiv] at hb
  convert hb using 1 <;> ext S <;> simp only [Finset.mem_image]

end LogicLineages.ModelsAlgebra.Forests.LaminarForestProof
