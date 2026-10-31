module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerConstructionTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamilyUlmProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
private theorem direct_sum_primary {ι : Type} {G : ι → Type}
    [∀ i, AddCommGroup (G i)] (p : ℕ)
    (h : ∀ i, ∀ x : G i, ∃ n : ℕ, p^n • x = 0) :
    ∀ x : DirectSum ι G, ∃ n : ℕ, p^n • x = 0 := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of i x =>
    obtain ⟨n, hn⟩ := h i x
    exact ⟨n, by rw [← map_nsmul, hn, map_zero]⟩
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n+m, ?_⟩
    rw [nsmul_add]
    have hnx : p^(n+m) • x = 0 := by
      rw [pow_add, mul_nsmul, hn, nsmul_zero]
    have hmy : p^(n+m) • y = 0 := by
      rw [pow_add, mul_comm, mul_nsmul, hm, nsmul_zero]
    rw [hnx, hmy, zero_add]

private theorem product_primary (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (hG : ∀ x : G, ∃ n : ℕ, p^n • x = 0) (hH : ∀ x : H, ∃ n : ℕ, p^n • x = 0) :
    ∀ x : G × H, ∃ n : ℕ, p^n • x = 0 := by
  intro x
  obtain ⟨n, hn⟩ := hG x.1
  obtain ⟨m, hm⟩ := hH x.2
  refine ⟨n+m, Prod.ext ?_ ?_⟩
  · change p^(n+m) • x.1 = 0
    rw [pow_add, mul_nsmul, hn, nsmul_zero]
  · change p^(n+m) • x.2 = 0
    rw [pow_add, mul_comm, mul_nsmul, hm, nsmul_zero]

private theorem rank_zero_of_stage_zero (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (α : Ordinal.{0}) (hz : (transfiniteFiltration p α : AddSubgroup G) = ⊥) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) = 0 := by
  apply (GroupInfinitary.ulm_rank_zero_socle p G _).mpr
  intro x hx
  have hx0 := hx.1
  change x ∈ transfiniteFiltration p α at hx0
  rw [hz] at hx0
  have he : x = 0 := hx0
  rw [he]
  exact (pStep p (transfiniteFiltration p α)).zero_mem

private theorem exact_length_successor (p : ℕ) (G : Type) [AddCommGroup G] (α : Ordinal.{0})
    (hn : (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥)
    (hz : (transfiniteFiltration p (α+1) : AddSubgroup G) = ⊥) :
    WalkerExactLength p G (α+1) := by
  refine ⟨hz, ?_⟩
  intro β hβ hb
  apply hn
  apply le_antisymm _ bot_le
  have h := transfiniteFiltration_antitone (G := G) p (Order.lt_add_one_iff.mp hβ)
  exact h.trans hb.le

theorem walker_construction_nature_length : Targets.walkerConstructionNatureLength := by
  classical
  intro p _ δ _ r hr
  have hp := (Fact.out : p.Prime)
  have hf := walker_source_families p δ r
  letI : Countable (δ+1).ToType := walker_countable_successor δ
  have hodd : ∀ x : WalkerOdd p δ r, ∃ n : ℕ, p^n • x = 0 :=
    product_primary p _ _ (walker_lower_reservoir p δ).2.1
      (direct_sum_primary p (fun _ => (walker_source_group_nature p δ).2.1))
  have heven : ∀ x : WalkerEven p δ r, ∃ n : ℕ, p^n • x = 0 :=
    product_primary p _ _ hodd
      (direct_sum_primary p (fun _ => (walker_source_group_nature p (δ+1)).2.1))
  have hoz := hf.2.2.2.2.1
  have hez := hf.2.2.2.2.2
  have hon : (transfiniteFiltration p δ : AddSubgroup (WalkerOdd p δ r)) ≠ ⊥ := by
    intro hzero
    have ht := (walker_family_ulm_table p δ r δ).1
    simp only [lt_self_iff_false, if_false, if_true] at ht
    have he := (rank_zero_of_stage_zero p _ δ hzero).symm.trans ht
    exact (Nat.ne_of_gt hr) (Nat.cast_injective (R := Cardinal) he.symm)
  have hen : (transfiniteFiltration p (δ+1) : AddSubgroup (WalkerEven p δ r)) ≠ ⊥ := by
    intro hzero
    have ht := (walker_family_ulm_table p δ r (δ+1)).2
    have hlt : δ < δ+1 := Order.lt_add_one_iff.mpr le_rfl
    simp only [not_lt.mpr hlt.le, if_false, hlt.ne', if_true] at ht
    have he := (rank_zero_of_stage_zero p _ (δ+1) hzero).symm.trans ht
    exact Cardinal.aleph0_ne_zero he.symm
  refine ⟨⟨hf.1, hodd, zero_stage_reduced _ p hp.ne_zero (δ+1) hoz⟩,
    ⟨hf.2.1, heven, zero_stage_reduced _ p hp.ne_zero (δ+2) hez⟩,
    exact_length_successor p _ δ hon hoz, ?_⟩
  have hz' : (transfiniteFiltration p ((δ+1)+1) : AddSubgroup (WalkerEven p δ r)) = ⊥ := by
    simpa only [add_assoc, one_add_one_eq_two] using hez
  have h := exact_length_successor p _ (δ+1) hen hz'
  simpa only [add_assoc, one_add_one_eq_two] using h

private theorem transfinite_rank_invariant (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α : AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  have hu := GroupInfinitary.injective_ulm_isomorphism G H p
    (transfiniteFiltration p α) e.toAddMonoidHom e.injective
  rw [hm] at hu
  obtain ⟨u⟩ := hu
  exact u.rank_eq

theorem walker_construction_distinct : Targets.walkerConstructionDistinct := by
  intro p _ δ _ r s hrs
  constructor
  · rintro ⟨e⟩
    have he := transfinite_rank_invariant p _ _ e δ
    have hr := (walker_family_ulm_table p δ r δ).1
    have hs := (walker_family_ulm_table p δ s δ).1
    simp only [lt_self_iff_false, if_false, if_true] at hr hs
    rw [hr, hs] at he
    exact hrs (Nat.cast_injective (R := Cardinal) he)
  · rintro ⟨e⟩
    have he := transfinite_rank_invariant p _ _ e δ
    have hr := (walker_family_ulm_table p δ r δ).2
    have hs := (walker_family_ulm_table p δ s δ).2
    simp only [lt_self_iff_false, if_false, if_true] at hr hs
    rw [hr, hs] at he
    exact hrs (Nat.cast_injective (R := Cardinal) he)
end LogicLineages.ModelsAlgebra.PGroups
