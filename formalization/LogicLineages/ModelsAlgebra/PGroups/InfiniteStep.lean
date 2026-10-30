module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteStepTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteStep
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem infinite_finite_step_ulm_rank : Targets.groupInfiniteFiniteStepUlmRank := by
  intro p _ G _ _ S hinf hstep
  letI : Infinite S := hinf
  letI : Countable (pSocle p S) := Subtype.val_injective.countable
  letI : Countable (UlmLayer p S) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S)).countable
  letI modQ : Module (ZMod p) (UlmLayer p S) := inferInstance
  letI freeQ : Module.Free (ZMod p) (UlmLayer p S) := Module.Free.of_divisionRing _ _
  apply le_antisymm
  · exact (rank_le_card (ZMod p) (UlmLayer p S)).trans Cardinal.mk_le_aleph0
  · by_contra hn
    have hr : Module.rank (ZMod p) (UlmLayer p S) < Cardinal.aleph0 := lt_of_not_ge hn
    letI finiteQ : Module.Finite (ZMod p) (UlmLayer p S) :=
      (@Module.rank_lt_aleph0_iff (ZMod p) (UlmLayer p S)
        (inferInstance : Semiring (ZMod p)) (inferInstance : AddCommMonoid (UlmLayer p S))
        modQ freeQ inferInstance).mp hr
    have hcard := @cardinal_lt_aleph0_of_finiteDimensional (ZMod p) (UlmLayer p S)
      (inferInstance : Ring (ZMod p)) inferInstance (inferInstance : AddCommGroup (UlmLayer p S))
      modQ inferInstance freeQ finiteQ
    have hq : Finite (UlmLayer p S) := Cardinal.mk_lt_aleph0_iff.mp hcard
    letI : Finite S := finite_step_finite_ulm G p S hstep hq
    exact (not_lt_of_ge (Cardinal.aleph0_le_mk S)) (Cardinal.lt_aleph0_of_finite S)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
