module
public import LogicLineages.OrdinalComparison.ConstantMonomialCountProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualConstantBudgetMonomialCount : Targets.ActualConstantBudgetMonomialCount :=
  actualConstantBudgetMonomialCount

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
