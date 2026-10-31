module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamilyUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamiliesProof
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
private theorem filtration_prod (p : ℕ) (α : Ordinal.{0}) (G H : Type)
    [AddCommGroup G] [AddCommGroup H] :
    (transfiniteFiltration p α : AddSubgroup (G × H)) =
      (transfiniteFiltration p α : AddSubgroup G).prod (transfiniteFiltration p α : AddSubgroup H) := by
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · simp only [transfiniteFiltration_zero]
    ext x
    simp
  · rw [transfiniteFiltration_add_one, ih, transfiniteFiltration_add_one,
      transfiniteFiltration_add_one]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hy.1, rfl⟩, ⟨y.2, hy.2, rfl⟩⟩
    · rintro ⟨⟨a, ha, heqa⟩, ⟨b, hb, heqb⟩⟩
      exact ⟨(a,b), ⟨ha,hb⟩, Prod.ext heqa heqb⟩
  · rw [transfiniteFiltration_limit p hβ, transfiniteFiltration_limit p hβ,
      transfiniteFiltration_limit p hβ]
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_prod]
    constructor
    · intro hx
      exact ⟨fun γ => (ih γ.1 γ.2 ▸ hx γ).1, fun γ => (ih γ.1 γ.2 ▸ hx γ).2⟩
    · rintro ⟨hx,hy⟩ γ
      rw [ih γ.1 γ.2]
      exact ⟨hx γ, hy γ⟩

private noncomputable def prod_stage_equiv (p : ℕ) (α : Ordinal.{0}) (G H : Type)
    [AddCommGroup G] [AddCommGroup H] :
    (transfiniteFiltration p α : AddSubgroup (G × H)) ≃+
      (↥(transfiniteFiltration p α : AddSubgroup G) × ↥(transfiniteFiltration p α : AddSubgroup H)) :=
  (AddEquiv.addSubgroupCongr (filtration_prod p α G H)).trans (AddSubgroup.prodEquiv _ _)

private theorem rank_tail_iso (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (δ : Ordinal.{0}) (e : (transfiniteFiltration p δ : AddSubgroup G) ≃+ H) (n : ℕ) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (δ+n) : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup H)) := by
  have ht := transfinite_tail_ulm_rank G p δ (n : Ordinal.{0})
  change Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n : Ordinal.{0}) :
    AddSubgroup (transfiniteFiltration p δ : AddSubgroup G))) = _ at ht
  rw [finite_ordinal_filtration] at ht
  exact ht.symm.trans (GroupInfinitary.isomorphism_ulm_rank _ H e p n)

private theorem rank_at_stage (p : ℕ) (G : Type) [AddCommGroup G] (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p 0 :
        AddSubgroup (transfiniteFiltration p α : AddSubgroup G))) := by
  have h := rank_tail_iso p G _ α (AddEquiv.refl _) 0
  rw [Nat.cast_zero, add_zero] at h
  exact h

private theorem rank_prod_transfinite (p : ℕ) [Fact p.Prime] (G H : Type)
    [AddCommGroup G] [AddCommGroup H] (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (G × H))) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) +
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) := by
  rw [rank_at_stage p (G × H) α,
    GroupInfinitary.isomorphism_ulm_rank _ _ (prod_stage_equiv p α G H) p 0,
    GroupInfinitary.product_ulm_rank,
    ← rank_at_stage p G α, ← rank_at_stage p H α]

private theorem countable_rank_bound (p : ℕ) (G : Type) [AddCommGroup G] [Countable G]
    (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤ Cardinal.aleph0 := by
  letI : Countable (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup G))).countable
  exact (rank_le_card (ZMod p) _).trans Cardinal.mk_le_aleph0

private theorem rank_zero_after (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (δ α : Ordinal.{0}) (hz : (transfiniteFiltration p δ : AddSubgroup G) = ⊥) (h : δ ≤ α) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) = 0 := by
  have he := le_antisymm ((transfiniteFiltration_antitone p h).trans hz.le) bot_le
  apply (GroupInfinitary.ulm_rank_zero_socle p G _).mpr
  intro x hx
  dsimp only at he
  have hx0 := hx.1
  change x ∈ transfiniteFiltration p α at hx0
  rw [he] at hx0
  have hxz : x = 0 := hx0
  rw [hxz]
  exact (pStep p (transfiniteFiltration p α)).zero_mem

private theorem pi_prime_rank (p : ℕ) [Fact p.Prime] (r n : ℕ) :
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup (Fin r → ZMod p))) =
      if n = 0 then (r : Cardinal) else 0 := by
  rw [GroupInfinitary.pi_ulm_rank]
  have hc : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup (ZMod p))) =
      if n = 0 then 1 else 0 := by
    have h := GroupInfinitary.cyclic_ulm_rank p 1 n
    change Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup (ZMod (p^1)))) = _ at h
    rw [pow_one] at h
    have hn : n+1=1 ↔ n=0 := by omega
    simp only [hn] at h
    exact h
  simp_rw [hc]
  by_cases hn : n = 0 <;> simp [hn]

private theorem omega_square_rank (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n :
      AddSubgroup (DirectSum ℕ (fun _ => ZMod (p^2))))) =
      if n = 1 then Cardinal.aleph0 else 0 := by
  rw [← finite_ordinal_filtration, transfinite_direct_sum_ulm_rank]
  have hc : Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n : Ordinal.{0}) : AddSubgroup (ZMod (p^2)))) =
      if n+1=2 then 1 else 0 := by
    rw [finite_ordinal_filtration]
    exact GroupInfinitary.cyclic_ulm_rank p 2 n
  change Cardinal.sum (fun _ : ℕ => Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n : Ordinal.{0}) : AddSubgroup (ZMod (p^2))))) = _
  rw [hc]
  by_cases hn : n = 1
  · subst n
    simp
  · have hne : n+1 ≠ 2 := by omega
    simp [hne, hn]

private theorem even_terminal_rank (p : ℕ) [Fact p.Prime] (r n : ℕ) :
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n :
      AddSubgroup ((Fin r → ZMod p) × DirectSum ℕ (fun _ => ZMod (p^2))))) =
      (if n = 0 then (r : Cardinal) else 0) + (if n = 1 then Cardinal.aleph0 else 0) := by
  rw [GroupInfinitary.product_ulm_rank, pi_prime_rank, omega_square_rank]

theorem walker_family_ulm_table : Targets.walkerFamilyUlmTable := by
  classical
  intro p _ δ _ r α
  have hf := walker_source_families p δ r
  letI : Countable (WalkerOdd p δ r) := hf.1
  letI : Countable (WalkerEven p δ r) := hf.2.1
  obtain ⟨eo⟩ := hf.2.2.1
  obtain ⟨ee⟩ := hf.2.2.2.1
  have hoz := hf.2.2.2.2.1
  have hez := hf.2.2.2.2.2
  by_cases hlow : α < δ
  · simp only [if_pos hlow]
    have hodd : Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerOdd p δ r))) = Cardinal.aleph0 := by
      apply le_antisymm (countable_rank_bound p _ α)
      rw [rank_prod_transfinite, walker_reservoir_ulm_rank, if_pos hlow]
      exact le_self_add
    refine ⟨hodd, le_antisymm (countable_rank_bound p _ α) ?_⟩
    rw [rank_prod_transfinite, hodd]
    exact le_self_add
  · simp only [if_neg hlow]
    by_cases heq : α = δ
    · subst α
      simp only [ite_true]
      constructor
      · have h := rank_tail_iso p (WalkerOdd p δ r) _ δ eo 0
        rw [Nat.cast_zero, add_zero, pi_prime_rank] at h
        simp only [ite_true] at h
        exact h
      · have h := rank_tail_iso p (WalkerEven p δ r) _ δ ee 0
        rw [Nat.cast_zero, add_zero, even_terminal_rank] at h
        simpa using h
    · simp only [if_neg heq]
      have hs : δ+1 ≤ α := Order.add_one_le_iff.mpr (lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm heq))
      refine ⟨rank_zero_after p _ (δ+1) α hoz hs, ?_⟩
      by_cases hnext : α = δ+1
      · subst α
        rw [if_pos rfl]
        have h := rank_tail_iso p (WalkerEven p δ r) _ δ ee 1
        rw [Nat.cast_one, even_terminal_rank] at h
        simpa using h
      · rw [if_neg hnext]
        apply rank_zero_after p _ (δ+2) α hez
        have h := Order.add_one_le_iff.mpr (lt_of_le_of_ne hs (Ne.symm hnext))
        simpa only [add_assoc, one_add_one_eq_two] using h
end LogicLineages.ModelsAlgebra.PGroups
