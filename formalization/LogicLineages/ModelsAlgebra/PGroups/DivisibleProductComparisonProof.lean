module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonTargets
public import LogicLineages.ModelsAlgebra.PGroups.ProductTransfiniteProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth
private theorem subgroup_atomic {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) : SubgroupComparison f 0 := by
  intro n b
  apply (zero_comparison H G n _ _).mpr
  have h₁ := embedding_atomic_agreement B H (C.subtype.comp f.toAddMonoidHom)
    (Subtype.val_injective.comp f.injective) n b
  have h₂ := embedding_atomic_agreement B G B.subtype Subtype.val_injective n b
  exact fun s t => (h₁ s t).symm.trans (h₂ s t)

private theorem two_mul_limit {γ : Ordinal} (hγ : Order.IsSuccLimit γ) : 2*γ=γ := by
  obtain ⟨ζ,hζ⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hγ.isSuccPrelimit
  rw [hζ,← mul_assoc]
  have htwo : (2:Ordinal)*Ordinal.omega0 = Ordinal.omega0 := by
    exact_mod_cast (Ordinal.natCast_mul_omega0 (by decide : 0 < (2:ℕ)))
  rw [htwo]

private theorem local_cut (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] (p:ℕ) [Fact p.Prime]
    (hG:∀x:G,∃k:ℕ,p^k • x=0) (hH:∀x:H,∃k:ℕ,p^k • x=0)
    (B:AddSubgroup G) (C:AddSubgroup H) [Finite B] (f:B≃+C) (γ:Ordinal.{0})
    (sG:SoclesInfiniteBelow p G (Ordinal.omega0*γ))
    (sH:SoclesInfiniteBelow p H (Ordinal.omega0*γ))
    (hRank:UlmRanksAgreeBelow p G H (Ordinal.omega0*γ))
    (hpres:MapCutsExact p f (Ordinal.omega0*γ)) : SubgroupComparison f (2*γ) := by
  have h := local_socle_back_forth G H p hG hH B C f
  rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨β,hβ⟩ | hγ
  · subst γ
    simpa only [mul_zero] using subgroup_atomic f
  · subst γ
    have hblock : Ordinal.omega0*β+Ordinal.omega0 = Ordinal.omega0*Order.succ β := by
      simp only [Order.succ_eq_add_one,mul_add_one]
    have hbound : Ordinal.omega0*β ≤ Ordinal.omega0*Order.succ β :=
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (Order.le_succ β)
    have hh := h.2.1 β
      (by simpa only [hblock] using sG) (by simpa only [hblock] using sH)
      (fun ξ hξ => hRank ξ (hξ.trans_le hbound))
      (fun ξ _ hξ => (hRank ξ (by simpa only [hblock] using hξ)).le)
      (by simpa only [hblock] using hpres)
    simpa only [Order.succ_eq_add_one,mul_add_one] using hh
  · rw [two_mul_limit hγ]
    exact h.2.2 γ hγ sG sH hRank hpres

private theorem divisible_stage_top (D : Type) [AddCommGroup D] (p : ℕ) (hp:p≠0)
    (hd : GroupDivisible D) (α : Ordinal.{0}) :
    (transfiniteFiltration p α : AddSubgroup D)=⊤ := by
  apply top_unique
  apply p_divisible_in_every_stage D p ⊤ _ α
  intro x
  obtain ⟨y,hy⟩ := hd p hp x
  exact ⟨⟨y,AddSubgroup.mem_top y⟩,Subtype.ext hy⟩

theorem divisible_product_data : Targets.divisibleProductData := by
  intro R D _ _ p _ hR hD hd
  refine ⟨?_,?_,?_⟩
  · intro x
    obtain ⟨k,hk⟩ := hR x.1
    obtain ⟨j,hj⟩ := hD x.2
    refine ⟨k+j,Prod.ext ?_ ?_⟩
    · change p^(k+j) • x.1=0
      rw [pow_add,mul_nsmul,hk,nsmul_zero]
    · change p^(k+j) • x.2=0
      rw [Nat.add_comm k j,pow_add,mul_nsmul,hj,nsmul_zero]
  · intro α x
    rw [product_transfinite_filtration,divisible_stage_top D p (Fact.out : p.Prime).ne_zero hd]
    simp only [AddSubgroup.mem_prod,AddSubgroup.mem_top,and_true]
  · intro α
    rw [product_transfinite_ulm_rank,divisible_stage_top D p (Fact.out : p.Prime).ne_zero hd]
    have hz : Module.rank (ZMod p) (UlmLayer p (⊤ : AddSubgroup D))=0 := by
      apply (GroupInfinitary.ulm_rank_zero_socle p D ⊤).mpr
      intro x _
      obtain ⟨y,hy⟩ := hd p (Fact.out : p.Prime).ne_zero x
      exact ⟨y,AddSubgroup.mem_top y,hy⟩
    rw [hz,add_zero]

private theorem product_socles (R D : Type) [AddCommGroup R] [AddCommGroup D]
    (p : ℕ) (δ : Ordinal.{0}) (sR:SoclesInfiniteBelow p R δ)
    (hm:∀ (α:Ordinal.{0}) (x:R×D), x∈transfiniteFiltration p α ↔ x.1∈transfiniteFiltration p α) :
    SoclesInfiniteBelow p (R×D) δ := by
  intro α hα
  letI := sR α hα
  let j : pSocle p (transfiniteFiltration p α : AddSubgroup R) →
      pSocle p (transfiniteFiltration p α : AddSubgroup (R×D)) := fun x =>
    ⟨((x:R),0),(hm α _).mpr x.property.1,by
      change p • ((x:R),(0:D))=0
      exact Prod.ext x.property.2 (nsmul_zero p)⟩
  apply Infinite.of_injective j
  intro x y h
  exact Subtype.ext (congrArg (fun z : pSocle p (transfiniteFiltration p α : AddSubgroup (R×D)) => (z:R×D).1) h)

theorem divisible_product_comparison : Targets.divisibleProductComparison := by
  intro R D E _ _ _ _ _ _ p _ hR hD hE hr hd he γ hl B C _ f hf
  have dD := divisible_product_data R D p hR hD hd
  have dE := divisible_product_data R E p hR hE he
  have sR : SoclesInfiniteBelow p R (Ordinal.omega0*γ) := by
    by_cases hz:γ=0
    · intro α hα
      simp only [hz,mul_zero,not_lt_zero] at hα
    · exact reduced_long_limit_infinite_socles R p hR hr _
        (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (lt_of_le_of_ne zero_le (Ne.symm hz))) hl
  apply local_cut (R×D) (R×E) p dD.1 dE.1 B C f γ
    (product_socles R D p _ sR dD.2.1) (product_socles R E p _ sR dE.2.1)
  · intro α _
    exact (dD.2.2 α).trans (dE.2.2 α).symm
  · intro x α _
    rw [dE.2.1,dD.2.1,hf]
end LogicLineages.ModelsAlgebra.PGroups
