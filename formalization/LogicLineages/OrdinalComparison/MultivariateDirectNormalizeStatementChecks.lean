module
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDirectNormalize.StatementChecks

theorem fixed_correspondence : Targets.MultivariateDirectNormalizeCorrespondence := correspondence
theorem fixed_source : Targets.MultivariateDirectNormalizeSource := source
theorem fixed_complete : Targets.MultivariateDirectNormalizeComplete := complete
theorem fixed_cap_independent : Targets.MultivariateCollectedCapIndependent := cap_independent

end LogicLineages.OrdinalComparison.MultivariateDirectNormalize.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariateDirectNormalize
