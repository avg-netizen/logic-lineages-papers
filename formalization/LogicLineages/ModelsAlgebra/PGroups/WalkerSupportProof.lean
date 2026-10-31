module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSupportTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerNormalProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem finite_ancestor_normal (p : ℕ) (hp : 0 < p) (ξ : Ordinal.{0})
    [Countable ξ.ToType] (S : Set (WalkerOrdinalNode ξ)) [Finite S]
    (hclosed : ∀ s ∈ S, ∀ t, walkerOrdinalParent ξ s = some t → t ∈ S)
    (x : WalkerSourceGroup p ξ)
    (hx : x ∈ AddSubgroup.closure (walkerPresentedGenerator p (walkerOrdinalParent ξ) '' S)) :
    ∃ d : WalkerOrdinalNode ξ →₀ ℕ,
      (∀ s, d s < p) ∧ (∀ s ∈ d.support, s ∈ S) ∧
        walkerDigitSum (walkerPresentedGenerator p (walkerOrdinalParent ξ)) d = x := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : LinearOrder S := LinearOrder.lift' (fun s : S => walkerOrdinalCode ξ s.val)
    ((walker_ordinal_coding ξ).1.comp Subtype.val_injective)
  let n := Fintype.card S
  let o : Fin n ≃o S := Fintype.orderIsoFinOfCardEq S rfl
  have hparent (i : Fin n) (t : WalkerOrdinalNode ξ)
      (h : walkerOrdinalParent ξ (o i).val = some t) :
      (o.symm ⟨t, hclosed _ (o i).property t h⟩).val < i.val := by
    have hc : (⟨t, hclosed _ (o i).property t h⟩ : S) < o i :=
      (walker_ordinal_coding ξ).2.2 _ _ h
    have hh : o.symm ⟨t, hclosed _ (o i).property t h⟩ < i := by
      simpa only [o.symm_apply_apply] using o.symm.strictMono hc
    exact hh
  let parent : WalkerParentSequence := fun k =>
    if hk : k < n then
      match h : walkerOrdinalParent ξ (o ⟨k,hk⟩).val with
      | none => none
      | some t => some ⟨(o.symm ⟨t, hclosed _ (o ⟨k,hk⟩).property t h⟩).val,
          hparent ⟨k,hk⟩ t h⟩
    else none
  let gen := walkerPresentedGenerator p (walkerOrdinalParent ξ)
  have hy : WalkerAssignmentRelations p parent n (fun i => gen (o i).val) := by
    intro i
    rw [walker_presented_relations (WalkerOrdinalNode ξ) p (walkerOrdinalParent ξ) (o i).val]
    simp only [parent, dif_pos i.isLt]
    split <;> simp_all [gen]
  obtain ⟨f, hf, _⟩ := walker_finite_universal p hp parent n (WalkerSourceGroup p ξ)
    (fun i => gen (o i).val) hy
  have hle : AddSubgroup.closure (gen '' S) ≤ f.range := by
    apply (AddSubgroup.closure_le f.range).mpr
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨i, hi⟩ := o.surjective ⟨s, hs⟩
    refine ⟨(walkerFinitePresentation p parent n).generator i, ?_⟩
    rw [hf]
    exact congrArg (fun t : S => gen t.val) hi
  obtain ⟨y, hyx⟩ := hle hx
  obtain ⟨a, ha⟩ := (walker_finite_tree_unique_digits p hp parent n).2 y
  let d0 : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  let emb : Fin n ↪ WalkerOrdinalNode ξ :=
    ⟨fun i => (o i).val, Subtype.val_injective.comp o.injective⟩
  let d := d0.embDomain emb
  refine ⟨d, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ Set.range emb
    · obtain ⟨i, rfl⟩ := hs
      change d0.embDomain emb (emb i) < p
      rw [Finsupp.embDomain_apply_self]
      exact (a i).isLt
    · change d0.embDomain emb s < p
      rw [Finsupp.embDomain_notin_range emb d0 s hs]
      exact hp
  · intro s hs
    change s ∈ (d0.embDomain emb).support at hs
    rw [Finsupp.support_embDomain] at hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hs
    exact (o i).property
  · rw [walkerDigitSum, Finsupp.sum_embDomain,
      Finsupp.sum_fintype d0 (fun i c => c • gen (emb i)) (fun _ => zero_nsmul _)]
    rw [← hyx, ← ha]
    simp only [walkerFiniteDigitSum, map_sum, map_nsmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hf]
    rfl

private theorem bounded_code_closure (p : ℕ) (ξ : Ordinal.{0}) [Countable ξ.ToType]
    (A : Set (WalkerOrdinalNode ξ)) (x : WalkerSourceGroup p ξ)
    (hx : x ∈ AddSubgroup.closure (walkerPresentedGenerator p (walkerOrdinalParent ξ) '' A)) :
    ∃ n : ℕ, x ∈ AddSubgroup.closure
      (walkerPresentedGenerator p (walkerOrdinalParent ξ) '' {s | s ∈ A ∧ walkerOrdinalCode ξ s < n}) := by
  let C (n : ℕ) := AddSubgroup.closure
    (walkerPresentedGenerator p (walkerOrdinalParent ξ) '' {s | s ∈ A ∧ walkerOrdinalCode ξ s < n})
  have hmono {n m : ℕ} (h : n ≤ m) : C n ≤ C m := by
    apply AddSubgroup.closure_mono
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, ⟨hs.1, lt_of_lt_of_le hs.2 h⟩, rfl⟩
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨walkerOrdinalCode ξ s + 1, AddSubgroup.subset_closure ⟨s, ⟨hs, Nat.lt_succ_self _⟩, rfl⟩⟩
  · exact ⟨0, (C 0).zero_mem⟩
  · intro x y _ _ hx hy
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m, (C _).add_mem (hmono (le_max_left _ _) hn) (hmono (le_max_right _ _) hm)⟩
  · intro x _ hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, (C n).neg_mem hn⟩

theorem walker_source_height_support : Targets.walkerSourceHeightSupport := by
  classical
  intro p hp ξ _ α d hd
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := bounded_code_closure p ξ {s | α ≤ walkerOrdinalHeight ξ s} _ hx
    let S : Set (WalkerOrdinalNode ξ) := {s | α ≤ walkerOrdinalHeight ξ s ∧ walkerOrdinalCode ξ s < n}
    letI : Finite S := Finite.of_injective
      (fun s : S => (⟨walkerOrdinalCode ξ s.val, s.property.2⟩ : Fin n)) (by
        intro s t h
        apply Subtype.ext
        apply (walker_ordinal_coding ξ).1
        exact congrArg Fin.val h)
    have hclosed : ∀ s ∈ S, ∀ t, walkerOrdinalParent ξ s = some t → t ∈ S := by
      intro s hs t h
      exact ⟨hs.1.trans (walker_ordinal_parent_height ξ s t h).le,
        lt_trans ((walker_ordinal_coding ξ).2.2 s t h) hs.2⟩
    obtain ⟨c, hc, hcs, hcx⟩ := finite_ancestor_normal p hp ξ S hclosed _ hn
    obtain ⟨a, _, hu⟩ := walker_source_unique_digits p hp ξ
      (walkerDigitSum (walkerPresentedGenerator p (walkerOrdinalParent ξ)) d)
    have hdc : d = c := (hu d ⟨hd, rfl⟩).trans (hu c ⟨hc, hcx⟩).symm
    subst d
    intro s hs
    exact (hcs s hs).1
  · intro hs
    apply (walkerHeightSpan p ξ α).sum_mem
    intro s hmem
    exact (walkerHeightSpan p ξ α).nsmul_mem (AddSubgroup.subset_closure ⟨s, hs s hmem, rfl⟩) _

end LogicLineages.ModelsAlgebra.PGroups
