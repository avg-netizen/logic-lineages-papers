module
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualControlledTraceFirstFinite : Targets.ActualControlledTraceFirstFinite :=
  actualControlledTraceFirstFinite
theorem fixed_actualLimitPartPrefixAddition : Targets.ActualLimitPartPrefixAddition := actualLimitPartPrefixAddition

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
