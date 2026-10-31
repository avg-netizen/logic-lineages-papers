module
public import LogicLineages.ModelsAlgebra.PGroups.ProductTransfiniteTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
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

theorem product_transfinite_filtration : Targets.productTransfiniteFiltration := by
  intro p G H _ _ α
  exact filtration_prod p α G H
theorem product_transfinite_ulm_rank : Targets.productTransfiniteUlmRank := rank_prod_transfinite
end LogicLineages.ModelsAlgebra.PGroups
