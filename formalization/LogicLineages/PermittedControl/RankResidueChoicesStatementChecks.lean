module
public import LogicLineages.PermittedControl.RankResidueChoicesTargets
import LogicLineages.PermittedControl.RankResidueChoicesCodeProof
import LogicLineages.PermittedControl.RankResidueChoicesLayoutProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_rankResidueLayoutAndChoices : RankResidueChoices.LayoutAndChoices :=
  ⟨RankResidueChoices.namedSlotsPrimitive,RankResidueChoices.choicesPrimitive,
    RankResidueChoices.namedSlotsExact,RankResidueChoices.choicesExact,
    RankResidueChoices.actualCellMember⟩

#print axioms fixed_rankResidueLayoutAndChoices

end LogicLineages.PermittedControl.StatementChecks
