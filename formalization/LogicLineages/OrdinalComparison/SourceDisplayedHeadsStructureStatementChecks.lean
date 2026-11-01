module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsStructureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads.StatementChecks

theorem fixed_validity : Targets.DisplayedSourceHeadValidity := validity
theorem fixed_budget : Targets.DisplayedSourceHeadOccurrenceBudget := budget
theorem fixed_argument_drop : Targets.DisplayedSourceArgumentDrop := argument_drop

end LogicLineages.OrdinalComparison.SourceDisplayedHeads.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads
