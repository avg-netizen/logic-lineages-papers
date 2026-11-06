module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionProof

theorem actualOriginalProgramComposition : InternalGraphCompositionTargets.ActualOriginalProgramComposition := by
  intro body m n f g hf hg uf ug
  exact ⟨InternalGraphCompositionTotalityProof.actualOriginalCompositionTotality body m n
    (OrdinaryArithmetic.graphFormula f) (fun i => OrdinaryArithmetic.graphFormula (g i)) hf hg,
    InternalGraphCompositionFunctionalityProof.actualOriginalCompositionFunctionality body m n
    (OrdinaryArithmetic.graphFormula f) (fun i => OrdinaryArithmetic.graphFormula (g i)) uf ug⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionProof
