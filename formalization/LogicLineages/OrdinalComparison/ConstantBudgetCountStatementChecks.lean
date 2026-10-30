module
public import LogicLineages.OrdinalComparison.ConstantBudgetCountProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualConstantBudgetCountCardinality : Targets.ActualConstantBudgetCountCardinality :=
  actualConstantBudgetCountCardinality

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
