module

public import LogicLineages.ModelsAlgebra.Forests.BinaryClusterTargets
public import Mathlib.Data.Finset.Max

/-! A compatible nonempty set belongs to a binary cluster family: choose a
smallest containing cluster and rule out descent into either binary child. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof

theorem binaryClusterUniverseNonempty : Targets.BinaryClusterUniverseNonempty := by
  intro α L family h
  exact (h.2.1 L h.1).1

theorem binaryClusterFamilyMaximal : Targets.BinaryClusterFamilyMaximal := by
  classical
  intro α L family h A hA hAL hcompat
  let containers := family.filter (fun B => A ⊆ B)
  have hnon : containers.Nonempty := ⟨L, Finset.mem_filter.mpr ⟨h.1, hAL⟩⟩
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image containers Finset.card hnon
  have hBfam := (Finset.mem_filter.mp hB).1
  have hAB := (Finset.mem_filter.mp hB).2
  rcases h.2.2.2.2 B hBfam with hBone | ⟨C, hC, D, hD, hCn, hDn, hdis, hjoin⟩
  · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by
      rw [hBone]
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr hA))
    exact heq ▸ hBfam
  · have hCB : C ⊆ B := by rw [← hjoin]; exact Finset.subset_union_left
    have hDB : D ⊆ B := by rw [← hjoin]; exact Finset.subset_union_right
    have hClt : C.card < B.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hCB, ?_⟩
      intro heq
      obtain ⟨d, hd⟩ := hDn
      have hdC : d ∈ C := heq ▸ hDB hd
      exact Finset.disjoint_left.mp hdis hdC hd
    have hDlt : D.card < B.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hDB, ?_⟩
      intro heq
      obtain ⟨c, hc⟩ := hCn
      have hcD : c ∈ D := heq ▸ hCB hc
      exact Finset.disjoint_left.mp hdis hc hcD
    have hnAC : ¬ A ⊆ C := fun hAC =>
      (not_lt_of_ge (hmin C (Finset.mem_filter.mpr ⟨hC, hAC⟩))) hClt
    have hnAD : ¬ A ⊆ D := fun hAD =>
      (not_lt_of_ge (hmin D (Finset.mem_filter.mpr ⟨hD, hAD⟩))) hDlt
    have hCA : C ⊆ A := by
      rcases hcompat C hC with hAC | hCA | hdisAC
      · exact False.elim (hnAC hAC)
      · exact hCA
      · apply False.elim
        apply hnAD
        intro z hz
        have hzB := hAB hz
        rw [← hjoin] at hzB
        rcases Finset.mem_union.mp hzB with hzC | hzD
        · exact False.elim (Finset.disjoint_left.mp hdisAC hz hzC)
        · exact hzD
    have hDA : D ⊆ A := by
      rcases hcompat D hD with hAD | hDA | hdisAD
      · exact False.elim (hnAD hAD)
      · exact hDA
      · apply False.elim
        apply hnAC
        intro z hz
        have hzB := hAB hz
        rw [← hjoin] at hzB
        rcases Finset.mem_union.mp hzB with hzC | hzD
        · exact hzC
        · exact False.elim (Finset.disjoint_left.mp hdisAD hz hzD)
    have hBA : B ⊆ A := by
      rw [← hjoin]
      exact Finset.union_subset hCA hDA
    have heq : A = B := Finset.Subset.antisymm hAB hBA
    exact heq ▸ hBfam

end LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof
