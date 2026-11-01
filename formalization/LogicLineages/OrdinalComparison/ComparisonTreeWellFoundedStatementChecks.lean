module
public import LogicLineages.OrdinalComparison.ComparisonTreeWellFoundedProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

theorem fixed_wellFounded : Targets.ActualNumericComparisonChildWellFounded := wellFounded

end LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonTree
