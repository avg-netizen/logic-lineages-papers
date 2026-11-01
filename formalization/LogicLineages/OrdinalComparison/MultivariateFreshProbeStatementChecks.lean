module
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateFreshProbe.StatementChecks

theorem fixed_head_source : Targets.PositiveVariableHeadSource := head_source
theorem fixed_source : Targets.MultivariateFreshProbeSource := source
theorem fixed_retraction : Targets.MultivariateFreshProbeRetraction := retraction

end LogicLineages.OrdinalComparison.MultivariateFreshProbe.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariateFreshProbe
