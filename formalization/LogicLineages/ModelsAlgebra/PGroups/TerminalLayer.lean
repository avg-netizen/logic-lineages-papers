module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalLayerTargets
public import LogicLineages.ModelsAlgebra.PGroups.RetainedSum
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem internal_sum_quotient_image : Targets.groupInternalSumQuotientImage := by
  classical
  intro G _ K T H hH hKT
  let q := QuotientAddGroup.mk' T
  let f : K →+ H.map q := (q.comp K.subtype).codRestrict (H.map q) (by
    intro x
    refine ⟨x, ?_, rfl⟩
    rw [hH]
    exact (le_sup_left : K ≤ K ⊔ T) x.property)
  have hf : Function.Injective f := by
    intro x y he
    have heq : q (x:G) = q (y:G) := congrArg Subtype.val he
    have ht : (x:G) - y ∈ T := QuotientAddGroup.eq_iff_sub_mem.mp heq
    exact Subtype.ext (sub_eq_zero.mp (AddSubgroup.disjoint_def.mp hKT
      (K.sub_mem x.property y.property) ht))
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨x,hx,hxz⟩ := z.property
    rw [hH] at hx
    obtain ⟨k,hk,t,ht,hkt⟩ := AddSubgroup.mem_sup.mp hx
    refine ⟨⟨k,hk⟩, Subtype.ext ?_⟩
    change q k = (z : G ⧸ T)
    rw [← hxz, ← hkt, map_add]
    have hz : q t = 0 := (QuotientAddGroup.eq_zero_iff t).mpr ht
    rw [hz, add_zero]
  exact ⟨AddEquiv.ofBijective f ⟨hf,hs⟩⟩

theorem terminal_layer_quotient : Targets.groupTerminalLayerQuotient := by
  intro G _ p δ K T hH hKT
  have hT : T ≤ (transfiniteFiltration p δ : AddSubgroup G) := by
    rw [hH]
    exact le_sup_right
  obtain ⟨e⟩ := internal_sum_quotient_image G K T (transfiniteFiltration p δ) hH hKT
  have he := quotient_filtration_below p T δ hT δ le_rfl
  rw [he]
  exact ⟨e.symm⟩

end LogicLineages.ModelsAlgebra.PGroups
