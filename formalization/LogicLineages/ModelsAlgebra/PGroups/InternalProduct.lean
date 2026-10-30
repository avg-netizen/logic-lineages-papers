module
public import LogicLineages.ModelsAlgebra.PGroups.InternalProductTargets
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem internal_product_isomorphism : Targets.groupInternalProductIsomorphism := by
  classical
  intro G _ K T H hH hKT
  let s : K × T →+ G := K.subtype.comp (AddMonoidHom.fst K T) +
    T.subtype.comp (AddMonoidHom.snd K T)
  let f : K × T →+ H := s.codRestrict H (by
    intro x
    rw [hH]
    exact AddSubgroup.add_mem_sup x.1.property x.2.property)
  have hf : Function.Injective f := by
    intro x y h
    have he := congrArg Subtype.val h
    change (x.1:G) + x.2 = (y.1:G) + y.2 at he
    have hd : (x.1:G) - y.1 = (y.2:G) - x.2 :=
      sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))
    have ht : (x.1:G) - y.1 ∈ T := by rw [hd]; exact T.sub_mem y.2.property x.2.property
    have hz := AddSubgroup.disjoint_def.mp hKT (K.sub_mem x.1.property y.1.property) ht
    have h1 : x.1 = y.1 := Subtype.ext (sub_eq_zero.mp hz)
    have he1 : (x.1:G) = y.1 := congrArg Subtype.val h1
    rw [he1] at he
    exact Prod.ext h1 (Subtype.ext (add_left_cancel he))
  have hs : Function.Surjective f := by
    intro x
    have hx : (x:G) ∈ K ⊔ T := hH ▸ x.property
    obtain ⟨k,hk,t,ht,hkt⟩ := AddSubgroup.mem_sup.mp hx
    exact ⟨(⟨k,hk⟩,⟨t,ht⟩), Subtype.ext hkt⟩
  exact ⟨AddEquiv.ofBijective f ⟨hf,hs⟩, fun _ => rfl⟩

end LogicLineages.ModelsAlgebra.PGroups
