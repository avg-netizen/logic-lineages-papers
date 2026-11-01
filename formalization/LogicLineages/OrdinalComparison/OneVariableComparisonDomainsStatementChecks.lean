module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDomainsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneVariableComparison.StatementChecks

theorem fixed_open_lower : Targets.ActualOneVariableOpenInputLowerBound := open_lower
theorem fixed_kernel_expansive : Targets.ActualSuffixKernelInputExpansive := kernel_expansive
theorem fixed_word_domains : Targets.ActualComparisonWordDomains := word_domains

end LogicLineages.OrdinalComparison.OneVariableComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.OneVariableComparison
