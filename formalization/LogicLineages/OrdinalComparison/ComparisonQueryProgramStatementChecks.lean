module
public import LogicLineages.OrdinalComparison.ComparisonQueryProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonQuery.StatementChecks

theorem fixed_program : Targets.ComparisonQueryProgramsPrimitiveRecursive := program

end LogicLineages.OrdinalComparison.ComparisonQuery.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonQuery
