module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiltrationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open Order

private theorem node_height_le (ξ : Ordinal.{0}) (s : WalkerOrdinalNode ξ) :
    walkerOrdinalHeight ξ s ≤ ξ := by
  rcases s with ⟨l, hl⟩
  cases l with
  | nil => exact le_rfl
  | cons a l => exact (Ordinal.typein_lt_self a).le

private theorem top_node (ξ : Ordinal.{0}) (s : WalkerOrdinalNode ξ)
    (h : ξ ≤ walkerOrdinalHeight ξ s) : s = walkerOrdinalRoot ξ := by
  rcases s with ⟨l, hl⟩
  cases l with
  | nil => rfl
  | cons a l => exact False.elim ((not_le_of_gt (Ordinal.typein_lt_self a)) h)

private theorem source_generator_ne_zero (p : ℕ) [Fact p.Prime] (ξ : Ordinal.{0})
    [Countable ξ.ToType] (s : WalkerOrdinalNode ξ) :
    walkerPresentedGenerator p (walkerOrdinalParent ξ) s ≠ 0 := by
  classical
  intro hz
  have hp := (Fact.out : p.Prime)
  let d : WalkerOrdinalNode ξ →₀ ℕ := Finsupp.single s 1
  have hd : ∀ t, d t < p := by
    intro t
    by_cases h : s = t
    · subst t; simpa [d] using hp.one_lt
    · simpa [d, Finsupp.single_apply, h] using hp.pos
  have hs : walkerDigitSum (walkerPresentedGenerator p (walkerOrdinalParent ξ)) d = 0 := by
    simpa [walkerDigitSum, d] using hz
  obtain ⟨a, _, hu⟩ := walker_source_unique_digits p hp.pos ξ 0
  have he : d = 0 := (hu d ⟨hd, hs⟩).trans
    (hu 0 ⟨fun _ => hp.pos, by simp [walkerDigitSum]⟩).symm
  have hh := congrArg (fun d : WalkerOrdinalNode ξ →₀ ℕ => d s) he
  simpa [d] using hh

private theorem cyclic_subgroup_equiv {G : Type} [AddCommGroup G] (x : G) (n : ℕ)
    (hx : addOrderOf x = n) : Nonempty (AddSubgroup.zmultiples x ≃+ ZMod n) := by
  let S := AddSubgroup.zmultiples x
  let sx : S := ⟨x, ⟨1, one_zsmul x⟩⟩
  have hgen : ∀ y : S, y ∈ AddSubgroup.zmultiples sx := by
    intro y
    obtain ⟨m, hm⟩ := y.property
    exact ⟨m, Subtype.ext hm⟩
  have hcard : Nat.card S = n := (Nat.card_zmultiples x).trans hx
  exact ⟨(zmodAddEquivOfGenerator hgen hcard).symm⟩

private theorem root_annihilated (p : ℕ) (ξ : Ordinal.{0}) :
    p • walkerPresentedGenerator p (walkerOrdinalParent ξ) (walkerOrdinalRoot ξ) = 0 := by
  simpa [walkerOrdinalParent, walkerOrdinalRoot] using
    walker_presented_relations (WalkerOrdinalNode ξ) p (walkerOrdinalParent ξ) (walkerOrdinalRoot ξ)

theorem walker_source_terminal : Targets.walkerSourceTerminal := by
  intro p _ ξ _
  have hp := (Fact.out : p.Prime)
  let r := walkerPresentedGenerator p (walkerOrdinalParent ξ) (walkerOrdinalRoot ξ)
  have hspan : walkerHeightSpan p ξ ξ = AddSubgroup.zmultiples r := by
    apply le_antisymm
    · apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨s, hs, rfl⟩
      rw [top_node ξ s hs]
      exact ⟨1, one_zsmul r⟩
    · apply AddSubgroup.zmultiples_le.mpr
      exact AddSubgroup.subset_closure ⟨walkerOrdinalRoot ξ, (by change ξ ≤ ξ; exact le_rfl), rfl⟩
  constructor
  · rw [walker_source_filtration p hp.pos ξ ξ, hspan]
    exact cyclic_subgroup_equiv r p (addOrderOf_eq_prime (root_annihilated p ξ)
      (source_generator_ne_zero p ξ (walkerOrdinalRoot ξ)))
  · rw [walker_source_filtration p hp.pos ξ (ξ+1)]
    apply le_antisymm _ bot_le
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨s, hs, rfl⟩
    exact False.elim ((not_le_of_gt (lt_add_one ξ)) (hs.trans (node_height_le ξ s)))

private theorem top_two_nodes (δ : Ordinal.{0}) (t : WalkerOrdinalNode (δ+1))
    (ht : walkerOrdinalParent (δ+1) t = some (walkerOrdinalRoot (δ+1)))
    (hheight : walkerOrdinalHeight (δ+1) t = δ) :
    ∀ s : WalkerOrdinalNode (δ+1), δ ≤ walkerOrdinalHeight (δ+1) s →
      s = walkerOrdinalRoot (δ+1) ∨ s = t := by
  rcases t with ⟨l, hl⟩
  cases l with
  | nil => simp [walkerOrdinalParent] at ht
  | cons b l =>
    have hl0 : l = [] := congrArg Subtype.val (Option.some.inj ht)
    subst l
    intro s hs
    rcases s with ⟨l, hl⟩
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      have ha : Ordinal.typein (α := (δ+1).ToType) (· < ·) a = δ :=
        le_antisymm (lt_add_one_iff.mp (Ordinal.typein_lt_self a)) hs
      have hab : a = b := Ordinal.typein_injective (α := (δ+1).ToType) (· < ·)
        (ha.trans hheight.symm)
      subst a
      cases l with
      | nil => exact Or.inr rfl
      | cons c l =>
        have hbc : b < c := List.rel_of_pairwise_cons hl (by simp)
        have hc : δ < Ordinal.typein (α := (δ+1).ToType) (· < ·) c := by
          exact lt_of_eq_of_lt hheight.symm
            ((Ordinal.typein_lt_typein (α := (δ+1).ToType) (· < ·)).mpr hbc)
        exact False.elim ((not_lt_of_ge (lt_add_one_iff.mp (Ordinal.typein_lt_self c))) hc)

theorem walker_source_double_terminal : Targets.walkerSourceDoubleTerminal := by
  intro p _ δ _
  have hp := (Fact.out : p.Prime)
  obtain ⟨t, ht, hh⟩ := walker_ordinal_children (δ+1) (walkerOrdinalRoot (δ+1)) δ (lt_add_one δ)
  let gen := walkerPresentedGenerator p (walkerOrdinalParent (δ+1))
  let r := gen (walkerOrdinalRoot (δ+1))
  have hpt : p • gen t = r := by
    simpa [ht] using walker_presented_relations (WalkerOrdinalNode (δ+1)) p (walkerOrdinalParent (δ+1)) t
  have hzero : p^2 • gen t = 0 := by
    rw [pow_two, mul_nsmul, hpt]
    exact root_annihilated p (δ+1)
  have horder : addOrderOf (gen t) = p^2 := by
    apply addOrderOf_eq_prime_pow (p := p) (n := 1)
    · simpa only [pow_one, hpt] using source_generator_ne_zero p (δ+1) (walkerOrdinalRoot (δ+1))
    · exact hzero
  have hspan : walkerHeightSpan p (δ+1) δ = AddSubgroup.zmultiples (gen t) := by
    apply le_antisymm
    · apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨s, hs, rfl⟩
      rcases top_two_nodes δ t ht hh s hs with rfl | rfl
      · change r ∈ AddSubgroup.zmultiples (gen t)
        rw [← hpt]
        exact (AddSubgroup.zmultiples (gen t)).nsmul_mem ⟨1, one_zsmul _⟩ p
      · exact ⟨1, one_zsmul _⟩
    · apply AddSubgroup.zmultiples_le.mpr
      exact AddSubgroup.subset_closure ⟨t, hh.ge, rfl⟩
  rw [walker_source_filtration p hp.pos (δ+1) δ, hspan]
  exact cyclic_subgroup_equiv (gen t) (p^2) horder

end LogicLineages.ModelsAlgebra.PGroups
