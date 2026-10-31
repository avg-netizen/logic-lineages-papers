module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelProof
public import LogicLineages.ModelsAlgebra.PGroups.ProductTransfiniteProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public import Mathlib.Data.Rat.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem pruefer_model_countable : Targets.prueferModelCountable := by
  intro p
  letI : Countable RationalModIntegers :=
    (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1:ℚ))).countable
  infer_instance

private theorem pruefer_stage_top (p:ℕ) [Fact p.Prime] (α:Ordinal.{0}) :
    (transfiniteFiltration p α : AddSubgroup (PrueferModel p))=⊤ := by
  apply top_unique
  apply p_divisible_in_every_stage (PrueferModel p) p ⊤ _ α
  intro x
  obtain ⟨y,hy⟩ := (genuine_pruefer_model p).2.1 p (Fact.out : p.Prime).ne_zero x
  exact ⟨⟨y,AddSubgroup.mem_top y⟩,Subtype.ext hy⟩

theorem pruefer_enlargement_data : Targets.prueferEnlargementData := by
  intro G _ _ p _ hG
  letI : Countable (PrueferModel p) := pruefer_model_countable p
  refine ⟨inferInstance,?_,?_,?_⟩
  · intro x
    obtain ⟨k,hk⟩ := hG x.1
    obtain ⟨j,hj⟩ := (genuine_pruefer_model p).1 x.2
    refine ⟨k+j,Prod.ext ?_ ?_⟩
    · change p^(k+j) • x.1=0
      rw [pow_add,mul_nsmul,hk,nsmul_zero]
    · change p^(k+j) • x.2=0
      rw [Nat.add_comm k j,pow_add,mul_nsmul,hj,nsmul_zero]
  · intro α x
    rw [product_transfinite_filtration,pruefer_stage_top]
    simp only [AddSubgroup.mem_prod,AddSubgroup.mem_top,and_true]
  · intro α
    rw [product_transfinite_ulm_rank,pruefer_stage_top]
    have hz : Module.rank (ZMod p) (UlmLayer p (⊤ : AddSubgroup (PrueferModel p)))=0 := by
      apply (GroupInfinitary.ulm_rank_zero_socle p (PrueferModel p) ⊤).mpr
      intro x _
      obtain ⟨y,hy⟩ := (genuine_pruefer_model p).2.1 p (Fact.out : p.Prime).ne_zero x
      exact ⟨y,AddSubgroup.mem_top y,hy⟩
    rw [hz,add_zero]

theorem reduced_pruefer_enlargement_noniso : Targets.reducedPrueferEnlargementNoniso := by
  intro G _ p _ hr ⟨e⟩
  let j : PrueferModel p →+ G := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr G (PrueferModel p))
  have hj : Function.Injective j := e.symm.injective.comp (by
    intro x y h
    exact congrArg Prod.snd h)
  have hd : ∀ n:ℕ, n≠0 → ∀ x:j.range, ∃ y:j.range, n • y=x := by
    intro n hn x
    obtain ⟨a,ha⟩ := x.property
    obtain ⟨b,hb⟩ := (genuine_pruefer_model p).2.1 n hn a
    refine ⟨⟨j b,⟨b,rfl⟩⟩,Subtype.ext ?_⟩
    change n • j b=(x:G)
    rw [←map_nsmul,hb,ha]
  have hz := hr j.range hd
  obtain ⟨t,ht,_⟩ := (genuine_pruefer_model p).2.2
  have hmem : j t∈j.range := ⟨t,rfl⟩
  rw [hz,AddSubgroup.mem_bot] at hmem
  exact ht (hj (hmem.trans j.map_zero.symm))
end LogicLineages.ModelsAlgebra.PGroups
