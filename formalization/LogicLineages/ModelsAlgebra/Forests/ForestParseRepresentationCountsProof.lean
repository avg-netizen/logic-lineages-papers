module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammarStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.Proof
open ForestParseRepresentationCotree ProfileAutomatonEncoding ForestParseRepresentationStates

theorem childCountExact : Targets.ChildCountExact := by
  intro M _ n c B
  classical
  rw [List.ofFn_eq_map]
  unfold CotreeGrammar.counts
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  simp only [List.toFinset_filter, List.toFinset_finRange, childCounts, Function.comp_def, beq_iff_eq]
  congr 1
  ext i
  simp

theorem stateCountExact : Targets.StateCountExact := by
  intro M _ o n c q
  rw [ForestParseRepresentationStatesGrammar.Proof.stateGrammarExact M o n c q]
  constructor
  · rintro ⟨w, hw, hp⟩
    refine ⟨w, hw, fun B => ?_⟩
    exact ((List.perm_iff_count.mp hp) B).trans (childCountExact M (n + 2) c B)
  · rintro ⟨w, hw, hc⟩
    refine ⟨w, hw, List.perm_iff_count.mpr (fun B => ?_)⟩
    exact (hc B).trans (childCountExact M (n + 2) c B).symm

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.Proof
