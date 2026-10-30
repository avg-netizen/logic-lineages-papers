module
public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminalTargets
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem coherent_terminal_quotient : Targets.groupCoherentTerminalQuotient := by
  classical
  intro G _ p δ K T hH hKT
  have hT : T ≤ (transfiniteFiltration p δ : AddSubgroup G) := by rw [hH]; exact le_sup_right
  have hQ := quotient_filtration_below p T δ hT δ le_rfl
  let q := QuotientAddGroup.mk' T
  let f : K →+ (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) :=
    (q.comp K.subtype).codRestrict _ (by
      intro x
      rw [hQ]
      refine ⟨x, ?_, rfl⟩
      rw [hH]
      exact (le_sup_left : K ≤ K ⊔ T) x.property)
  have hf : Function.Injective f := by
    intro x y he
    have heq : q (x:G) = q (y:G) := congrArg Subtype.val he
    have ht : (x:G)-y ∈ T := QuotientAddGroup.eq_iff_sub_mem.mp heq
    exact Subtype.ext (sub_eq_zero.mp (AddSubgroup.disjoint_def.mp hKT
      (K.sub_mem x.property y.property) ht))
  have hs : Function.Surjective f := by
    intro z
    have hz : (z : G ⧸ T) ∈ (transfiniteFiltration p δ : AddSubgroup G).map q := hQ.le z.property
    obtain ⟨x,hx,hxz⟩ := hz
    rw [hH] at hx
    obtain ⟨k,hk,t,ht,hkt⟩ := AddSubgroup.mem_sup.mp hx
    refine ⟨⟨k,hk⟩, Subtype.ext ?_⟩
    change q k = (z : G ⧸ T)
    rw [← hxz, ← hkt, map_add]
    have ht0 : q t = 0 := (QuotientAddGroup.eq_zero_iff t).mpr ht
    rw [ht0, add_zero]
  exact ⟨AddEquiv.ofBijective f ⟨hf,hs⟩, fun _ => rfl⟩

end LogicLineages.ModelsAlgebra.PGroups
