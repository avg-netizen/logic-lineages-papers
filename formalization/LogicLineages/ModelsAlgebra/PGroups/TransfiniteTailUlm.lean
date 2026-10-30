module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe v

theorem transfinite_tail_ulm_isomorphism : Targets.groupTransfiniteTailUlmIsomorphism.{v} := by
  intro G _ p δ β
  let H := (transfiniteFiltration p δ : AddSubgroup G)
  have he := GroupInfinitary.injective_ulm_isomorphism H G p (transfiniteFiltration p β)
    H.subtype Subtype.val_injective
  rw [transfinite_tail_image] at he
  exact he

theorem transfinite_tail_ulm_rank : Targets.groupTransfiniteTailUlmRank.{v} := by
  intro G _ p δ β
  obtain ⟨e⟩ := transfinite_tail_ulm_isomorphism G p δ β
  exact e.rank_eq

end LogicLineages.ModelsAlgebra.PGroups
