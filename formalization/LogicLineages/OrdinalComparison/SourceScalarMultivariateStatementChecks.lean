module
public import LogicLineages.OrdinalComparison.SourceScalarMultivariateProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateSourceBridge.StatementChecks

theorem fixed_raw_omega_without : Targets.RawOmegaNoFinitePart := raw_omega_without
theorem fixed_head_limit : Targets.SourceScalarFixedLimit := head_limit
theorem fixed_adapter : Targets.SourceScalarMultivariateAdapter := adapter

end LogicLineages.OrdinalComparison.MultivariateSourceBridge.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariateSourceBridge
