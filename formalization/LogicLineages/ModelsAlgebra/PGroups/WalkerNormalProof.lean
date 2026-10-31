module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerNormalTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerRealizationProof
public import Mathlib.Data.Finset.Lattice.Fold
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem finite_normal (p : ℕ) (hp : 0 < p) (parent : WalkerParentSequence) (n : ℕ) :
    WalkerDigitNormalForm p (walkerFinitePresentation p parent n).generator := by
  classical
  intro x
  obtain ⟨a, ha⟩ := (walker_finite_tree_unique_digits p hp parent n).2 x
  let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  have hd : walkerDigitSum (walkerFinitePresentation p parent n).generator d = x := by
    rw [walkerDigitSum, Finsupp.sum_fintype d (fun i c => c • (walkerFinitePresentation p parent n).generator i) (fun _ => zero_nsmul _)]
    exact ha
  refine ⟨d, ⟨fun i => (a i).isLt, hd⟩, ?_⟩
  intro c hc
  let b : Fin n → Fin p := fun i => ⟨c i, hc.1 i⟩
  have hb : walkerFiniteDigitSum p parent n b = x := by
    rw [← hc.2, walkerDigitSum, Finsupp.sum_fintype c (fun i c => c • (walkerFinitePresentation p parent n).generator i) (fun _ => zero_nsmul _)]
    rfl
  have hba := (walker_finite_tree_unique_digits p hp parent n).1 (hb.trans ha.symm)
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun hba i)

private theorem sequential_sum_bound (p : ℕ) (parent : WalkerParentSequence)
    (d : ℕ →₀ ℕ) (n : ℕ) (hs : d.support ⊆ Finset.range n) :
    walkerDigitSum (walkerSequentialGenerator p parent) d =
      walkerStageInclusion p parent n
        (∑ i : Fin n, d i.val • (walkerFinitePresentation p parent n).generator i) := by
  rw [walkerDigitSum, Finsupp.sum_of_support_subset d hs (fun i c => c • walkerSequentialGenerator p parent i) (fun _ _ => zero_nsmul _), Finset.sum_range]
  simp only [map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [walker_limit_generators p parent n i]

private theorem sequential_digits_injective (p : ℕ) (hp : 0 < p) (parent : WalkerParentSequence)
    (d c : ℕ →₀ ℕ) (hd : ∀ i, d i < p) (hc : ∀ i, c i < p)
    (he : walkerDigitSum (walkerSequentialGenerator p parent) d =
      walkerDigitSum (walkerSequentialGenerator p parent) c) : d = c := by
  classical
  let S := d.support ∪ c.support
  let n := (S.sup id).succ
  have hS : S ⊆ Finset.range n := Finset.subset_range_sup_succ S
  have hD : d.support ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_left hS
  have hC : c.support ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_right hS
  rw [sequential_sum_bound p parent d n hD, sequential_sum_bound p parent c n hC] at he
  have hs := walker_limit_faithful p hp parent n he
  let a : Fin n → Fin p := fun i => ⟨d i.val, hd i.val⟩
  let b : Fin n → Fin p := fun i => ⟨c i.val, hc i.val⟩
  have hab : a = b := (walker_finite_tree_unique_digits p hp parent n).1 hs
  apply Finsupp.ext
  intro i
  by_cases hi : i < n
  · exact congrArg Fin.val (congrFun hab ⟨i, hi⟩)
  · have hid : i ∉ d.support := fun hm => hi (Finset.mem_range.mp (hD hm))
    have hic : i ∉ c.support := fun hm => hi (Finset.mem_range.mp (hC hm))
    rw [Finsupp.notMem_support_iff.mp hid, Finsupp.notMem_support_iff.mp hic]

private theorem sequential_normal (p : ℕ) (hp : 0 < p) (parent : WalkerParentSequence) :
    WalkerDigitNormalForm p (walkerSequentialGenerator p parent) := by
  classical
  intro x
  obtain ⟨n, a, ha⟩ := walker_limit_digits p hp parent x
  let d0 : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  let emb : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let d := d0.embDomain emb
  have hd (i : ℕ) : d i < p := by
    by_cases hi : i ∈ Set.range emb
    · obtain ⟨j, rfl⟩ := hi
      change d0.embDomain emb (emb j) < p
      rw [Finsupp.embDomain_apply_self]
      exact (a j).isLt
    · change d0.embDomain emb i < p
      rw [Finsupp.embDomain_notin_range emb d0 i hi]
      exact hp
  have he : walkerDigitSum (walkerSequentialGenerator p parent) d = x := by
    rw [walkerDigitSum, Finsupp.sum_embDomain, Finsupp.sum_fintype d0 (fun i c => c • walkerSequentialGenerator p parent (emb i)) (fun _ => zero_nsmul _)]
    rw [← ha]
    simp only [walkerFiniteDigitSum, map_sum, map_nsmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [walker_limit_generators p parent n i]
    rfl
  refine ⟨d, ⟨hd, he⟩, ?_⟩
  intro c hc
  exact sequential_digits_injective p hp parent c d hc.1 hd (hc.2.trans he.symm)

private theorem normal_transport (I V X Y : Type) [AddCommGroup X] [AddCommGroup Y]
    (p : ℕ) (e : I ≃ V) (f : X ≃+ Y) (gx : V → X) (gy : I → Y)
    (hf : ∀ i, f (gx (e i)) = gy i) (hn : WalkerDigitNormalForm p gy) :
    WalkerDigitNormalForm p gx := by
  classical
  let D : (I →₀ ℕ) ≃ (V →₀ ℕ) := Finsupp.equivCongrLeft e
  have hsum (d : I →₀ ℕ) : f (walkerDigitSum gx (D d)) = walkerDigitSum gy d := by
    change f ((Finsupp.equivMapDomain e d).sum (fun v c => c • gx v)) = _
    rw [Finsupp.sum_equivMapDomain]
    simp only [walkerDigitSum, Finsupp.sum, map_sum, map_nsmul, hf]
  intro x
  obtain ⟨d, hd, hu⟩ := hn (f x)
  refine ⟨D d, ⟨?_, ?_⟩, ?_⟩
  · intro v
    exact hd.1 (e.symm v)
  · apply f.injective
    exact (hsum d).trans hd.2
  · intro c hc
    have hcD : (∀ i, (D.symm c) i < p) ∧ walkerDigitSum gy (D.symm c) = f x := by
      constructor
      · intro i
        exact hc.1 (e i)
      · rw [← hsum, D.apply_symm_apply]
        exact congrArg f hc.2
    have he := hu (D.symm c) hcD
    exact (D.apply_symm_apply c).symm.trans (congrArg D he)

theorem walker_source_unique_digits : Targets.walkerSourceUniqueDigits := by
  intro p hp ξ _
  rcases walker_source_realization p hp ξ with ⟨n, e, he, f, hf⟩ | ⟨e, he, f, hf⟩
  · exact normal_transport _ _ _ _ p e f _ _ hf
      (finite_normal p hp (walkerFiniteOrdinalParent ξ n e he) n)
  · exact normal_transport _ _ _ _ p e f _ _ hf
      (sequential_normal p hp (walkerInfiniteOrdinalParent ξ e he))

end LogicLineages.ModelsAlgebra.PGroups
