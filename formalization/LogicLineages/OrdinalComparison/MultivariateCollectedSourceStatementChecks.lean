module
public import LogicLineages.OrdinalComparison.MultivariateCollectedSourceProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateCollected.StatementChecks

theorem fixed_probe_shape : Targets.MultivariateCollectedProbeShape := probe_shape
theorem fixed_decode : Targets.MultivariateCollectedDecodeSemantics := decode_semantics
theorem fixed_source : Targets.MultivariateCollectedSourceSemantics := source_semantics

end LogicLineages.OrdinalComparison.MultivariateCollected.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariateCollected
