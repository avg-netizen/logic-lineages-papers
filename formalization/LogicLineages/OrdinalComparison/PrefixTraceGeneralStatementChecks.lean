module
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPrefixControlStep : Targets.ActualPrefixControlStep := actualPrefixControlStep
theorem fixed_actualPrefixControlTrace : Targets.ActualPrefixControlTrace := actualPrefixControlTrace

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
