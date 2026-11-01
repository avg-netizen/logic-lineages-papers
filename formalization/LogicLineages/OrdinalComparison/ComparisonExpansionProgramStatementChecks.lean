module
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion.StatementChecks

theorem fixed_prefix : Targets.ComparisonRangePrefixProgram := prefix_program
theorem fixed_program : Targets.ComparisonExpansionProgram := program

end LogicLineages.OrdinalComparison.ComparisonExpansion.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonExpansion
