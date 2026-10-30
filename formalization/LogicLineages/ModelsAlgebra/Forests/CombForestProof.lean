module

public import LogicLineages.ModelsAlgebra.Forests.CombForestTargets
public import LogicLineages.ModelsAlgebra.Forests.LaminarForestProof
public import Lean.Elab.Tactic.Omega

/-! The concrete comb pays all binary-splitting and actual-forest obligations.
Its only nonsingleton clusters are suffixes, which are linearly nested. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CombForestProof

theorem singleton_compatible {α : Type} (a : α) (B : Finset α) :
    ClusterCompatible {a} B := by
  classical
  by_cases ha : a ∈ B
  · exact Or.inl (Finset.singleton_subset_iff.mpr ha)
  · right; right
    exact Finset.disjoint_singleton_left.mpr ha

theorem compatible_symm {α : Type} {A B : Finset α}
    (h : ClusterCompatible A B) : ClusterCompatible B A := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h.symm)

private theorem suffix_nested (m : Nat) (i j : Fin m) :
    combSuffix m i ⊆ combSuffix m j ∨ combSuffix m j ⊆ combSuffix m i := by
  rcases le_total i j with hij | hji
  · right
    intro k hk
    simp only [combSuffix, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hij hk
  · left
    intro k hk
    simp only [combSuffix, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hji hk

private theorem suffix_nonempty (m : Nat) (k : Fin m) : (combSuffix m k).Nonempty :=
  ⟨k, by simp [combSuffix]⟩

private theorem singleton_mem (m : Nat) (k : Fin m) : {k} ∈ combFamily m :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

private theorem suffix_mem (m : Nat) (k : Fin m) : combSuffix m k ∈ combFamily m :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

theorem combFamilyBinary : Targets.CombFamilyBinary := by
  intro m hm
  have hzero : combSuffix m ⟨0, hm⟩ = Finset.univ := by
    ext i; simp [combSuffix, Fin.le_def]
  refine ⟨hzero ▸ suffix_mem m ⟨0, hm⟩, ?_, ?_, ?_, ?_⟩
  · intro B hB
    refine ⟨?_, Finset.subset_univ B⟩
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.singleton_nonempty i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact suffix_nonempty m i
  · intro i _; exact singleton_mem m i
  · intro A hA B hB
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact singleton_compatible i B
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
        exact compatible_symm (singleton_compatible j (combSuffix m i))
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
        rcases suffix_nested m i j with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      left; exact Finset.card_singleton _
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
      by_cases hk : k.val + 1 < m
      · let j : Fin m := ⟨k.val + 1, hk⟩
        right
        refine ⟨{k}, singleton_mem m k, combSuffix m j, suffix_mem m j,
          Finset.singleton_nonempty k, suffix_nonempty m j, ?_, ?_⟩
        · apply Finset.disjoint_singleton_left.mpr
          simp only [combSuffix, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, j]
          omega
        · ext i
          simp only [Finset.mem_union, Finset.mem_singleton, combSuffix, Finset.mem_filter,
            Finset.mem_univ, true_and, Fin.le_def, Fin.ext_iff, j]
          omega
      · have heq : combSuffix m k = {k} := by
          ext i
          simp only [combSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, Fin.ext_iff, Fin.le_def]
          omega
        left; rw [heq]; exact Finset.card_singleton _

theorem combNontrivialClustersNested : Targets.CombNontrivialClustersNested := by
  intro m A B hA hB hAc hBc
  rcases Finset.mem_union.mp hA with hA | hA
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    simp only [Finset.card_singleton] at hAc
    omega
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      simp only [Finset.card_singleton] at hBc
      omega
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      exact suffix_nested m i j

theorem actualCombForest : Targets.ActualCombForest := by
  classical
  intro m hm
  obtain ⟨F, nodes, leaves, _, hmem, _, hbinary⟩ :=
    LaminarForestProof.binaryFamilyForestRepresentation (Fin m) (combFamily m) (combFamilyBinary m hm)
  have hcluster (B : combFamily m) : finiteLeafCluster F (nodes B) = B.val.map leaves.toEmbedding := by
    ext ℓ
    obtain ⟨a, rfl⟩ := leaves.surjective ℓ
    simpa only [finiteLeafCluster, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map_equiv, Equiv.symm_apply_apply] using hmem B a
  refine ⟨F, hbinary, ?_, ?_⟩
  · have hcard := Fintype.card_congr leaves
    simpa only [Fintype.card_fin, Fintype.card_subtype, leafFinset] using hcard.symm
  · intro u v hu hv
    obtain ⟨B, rfl⟩ := nodes.surjective u
    obtain ⟨C, rfl⟩ := nodes.surjective v
    rw [hcluster B] at hu
    rw [hcluster C] at hv
    simp only [Finset.card_map] at hu hv
    rw [hcluster B, hcluster C]
    rcases combNontrivialClustersNested m B.val C.val B.property C.property hu hv with h | h
    · exact Or.inl (Finset.map_subset_map.mpr h)
    · exact Or.inr (Finset.map_subset_map.mpr h)

end LogicLineages.ModelsAlgebra.Forests.CombForestProof
