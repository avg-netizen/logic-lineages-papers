module
public import LogicLineages.OrdinalComparison.OmegaBlockPrefixProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualRetainedPrefixOmegaBlock : Targets.ActualRetainedPrefixOmegaBlock := actualRetainedPrefixOmegaBlock
theorem fixed_fullActualOmegaBlock : Targets.FullActualOmegaBlock := fullActualOmegaBlock

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
