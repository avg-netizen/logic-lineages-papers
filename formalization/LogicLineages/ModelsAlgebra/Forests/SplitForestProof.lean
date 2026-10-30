module

public import LogicLineages.ModelsAlgebra.Forests.SplitForestTargets
public import LogicLineages.ModelsAlgebra.Forests.CombForestProof

/-! A concrete root split 2+(m−2) with singleton leaves. The second child may
multifurcate; only the first (comb) witness needs maximal binary clusters. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.SplitForestProof

open CombForestProof

private theorem parts_disjoint (m : Nat) : Disjoint (splitLeft m) (splitRight m) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [splitLeft, splitRight, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  omega

theorem splitFamilyLaminar : Targets.SplitFamilyLaminar := by
  intro m hm
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.singleton_nonempty i
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      · exact ⟨⟨0, by omega⟩, by simp [splitLeft]⟩
      · exact ⟨⟨2, by omega⟩, by simp [splitRight]⟩
  · intro i
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · intro A hA B hB
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact singleton_compatible i B
    · rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
        exact compatible_symm (singleton_compatible i A)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
        rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl
        all_goals first
          | exact Or.inl (Finset.subset_univ _)
          | exact Or.inr (Or.inl (Finset.subset_univ _))
          | exact Or.inl (Finset.Subset.refl _)
          | exact Or.inr (Or.inr (parts_disjoint m))
          | exact Or.inr (Or.inr (parts_disjoint m).symm)

theorem actualSplitForest : Targets.ActualSplitForest := by
  classical
  intro m hm
  obtain ⟨F, nodes, leaves, _, hmem, _⟩ :=
    LaminarForestProof.laminarFamilyForestRepresentation (Fin m) (splitFamily m) (splitFamilyLaminar m hm)
  have hcluster (B : splitFamily m) : finiteLeafCluster F (nodes B) = B.val.map leaves.toEmbedding := by
    ext ℓ
    obtain ⟨a, rfl⟩ := leaves.surjective ℓ
    simpa only [finiteLeafCluster, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map_equiv, Equiv.symm_apply_apply] using hmem B a
  have hl : splitLeft m ∈ splitFamily m := by simp [splitFamily]
  have hr : splitRight m ∈ splitFamily m := by simp [splitFamily]
  have hlcard : 2 ≤ (splitLeft m).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨⟨0, by omega⟩, by simp [splitLeft], ⟨1, by omega⟩, by simp [splitLeft], ?_⟩
    intro heq
    exact (by decide : (0 : Nat) ≠ 1) (congrArg Fin.val heq)
  have hrcard : 2 ≤ (splitRight m).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨⟨2, by omega⟩, by simp [splitRight], ⟨3, by omega⟩, by simp [splitRight], ?_⟩
    intro heq
    exact (by decide : (2 : Nat) ≠ 3) (congrArg Fin.val heq)
  refine ⟨F, ?_, nodes ⟨splitLeft m, hl⟩, nodes ⟨splitRight m, hr⟩, ?_⟩
  · have hcard := Fintype.card_congr leaves
    simpa only [Fintype.card_fin, Fintype.card_subtype, leafFinset] using hcard.symm
  · rw [hcluster ⟨splitLeft m, hl⟩, hcluster ⟨splitRight m, hr⟩]
    exact ⟨(Finset.disjoint_map leaves.toEmbedding).mpr (parts_disjoint m),
      by simpa only [Finset.card_map] using hlcard,
      by simpa only [Finset.card_map] using hrcard⟩

end LogicLineages.ModelsAlgebra.Forests.SplitForestProof
