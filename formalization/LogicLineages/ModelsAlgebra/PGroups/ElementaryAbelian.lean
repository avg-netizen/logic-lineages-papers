module

public import LogicLineages.ModelsAlgebra.PGroups.ElementaryAbelianTargets
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u


theorem elementary_abelian_rank : Targets.groupElementaryAbelianRank.{u} := by
  intro p _ G _ _ _ h
  letI modG : Module (ZMod p) G := AddCommGroup.zmodModule h
  letI freeG : Module.Free (ZMod p) G := Module.Free.of_divisionRing (ZMod p) G
  apply le_antisymm
  · exact (rank_le_card (ZMod p) G).trans Cardinal.mk_le_aleph0
  · by_contra hn
    have hr : Module.rank (ZMod p) G < Cardinal.aleph0 := lt_of_not_ge hn
    letI finiteG : Module.Finite (ZMod p) G := (@Module.rank_lt_aleph0_iff (ZMod p) G (inferInstance : Semiring (ZMod p)) (inferInstance : AddCommMonoid G) modG freeG inferInstance).mp hr
    exact (not_lt_of_ge (Cardinal.aleph0_le_mk G))
      (@cardinal_lt_aleph0_of_finiteDimensional (ZMod p) G (inferInstance : Ring (ZMod p)) inferInstance (inferInstance : AddCommGroup G) modG inferInstance freeG finiteG)

theorem elementary_abelian_isomorphism : Targets.groupElementaryAbelianIsomorphism.{u} := by
  intro p _ G H _ _ _ _ _ _ hG hH
  letI modG : Module (ZMod p) G := AddCommGroup.zmodModule hG
  letI modH : Module (ZMod p) H := AddCommGroup.zmodModule hH
  letI freeG : Module.Free (ZMod p) G := Module.Free.of_divisionRing (ZMod p) G
  letI freeH : Module.Free (ZMod p) H := Module.Free.of_divisionRing (ZMod p) H
  have hrG : Module.rank (ZMod p) G = Cardinal.aleph0 := elementary_abelian_rank p G hG
  have hrH : Module.rank (ZMod p) H = Cardinal.aleph0 := elementary_abelian_rank p H hH
  obtain ⟨e⟩ := @nonempty_linearEquiv_of_rank_eq (ZMod p) G H (inferInstance : Semiring (ZMod p)) (inferInstance : AddCommMonoid G) modG freeG (inferInstance : AddCommMonoid H) modH freeH inferInstance (hrG.trans hrH.symm)
  exact ⟨e.toAddEquiv⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
