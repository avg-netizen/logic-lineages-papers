module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerCompleteTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGroupNatureProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_full_source_lemma : Targets.walkerFullSourceLemma := by
  intro p _
  have hp := (Fact.out : p.Prime)
  constructor
  · intro ξ _
    have hn := walker_source_group_nature p ξ
    refine ⟨hn.1, hn.2.1, hn.2.2, walker_source_unique_digits p hp.pos ξ,
      walker_source_filtration p hp.pos ξ, ?_, (walker_source_terminal p ξ).1,
      (walker_source_terminal p ξ).2⟩
    rw [walker_source_filtration p hp.pos ξ ξ]
    apply le_antisymm
    · apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨s, hs, rfl⟩
      have hroot : s = walkerOrdinalRoot ξ := by
        rcases s with ⟨l, hl⟩
        cases l with
        | nil => rfl
        | cons a l => exact False.elim ((not_le_of_gt (Ordinal.typein_lt_self a)) hs)
      rw [hroot]
      exact ⟨1, one_zsmul _⟩
    · apply AddSubgroup.zmultiples_le.mpr
      exact AddSubgroup.subset_closure
        ⟨walkerOrdinalRoot ξ, (by change ξ ≤ ξ; exact le_rfl), rfl⟩
  · intro δ _
    letI : Countable (δ+1).ToType := walker_countable_successor δ
    exact walker_source_double_terminal p δ

end LogicLineages.ModelsAlgebra.PGroups
