module
public import LogicLineages.ModelsAlgebra.PGroups.InternalProjectionTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationRetraction
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem internal_projection_existence : Targets.groupInternalProjectionExistence := by
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
  let e := AddEquiv.ofBijective f ⟨hf,hs⟩
  refine ⟨(AddMonoidHom.fst K T).comp e.symm.toAddMonoidHom, ?_⟩
  intro x
  have he : e (x,0) = (⟨x, by rw [hH]; exact (le_sup_left : K ≤ K ⊔ T) x.property⟩ : H) := by
    apply Subtype.ext
    change (x:G) + 0 = x
    exact add_zero _
  change (e.symm _).1 = x
  rw [← he, e.symm_apply_apply]

theorem internal_summand_filtration : Targets.groupInternalSummandFiltration := by
  intro G _ K T H hH hKT p α x
  have hK : K ≤ H := by rw [hH]; exact le_sup_left
  let i := AddSubgroup.inclusion hK
  obtain ⟨r,hr⟩ := internal_projection_existence G K T H hH hKT
  exact retraction_filtration_reflection K H i r hr p α x

end LogicLineages.ModelsAlgebra.PGroups
