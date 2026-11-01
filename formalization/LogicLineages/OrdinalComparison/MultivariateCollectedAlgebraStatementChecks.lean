module
public import LogicLineages.OrdinalComparison.MultivariateCollectedAlgebraProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateCollected.StatementChecks

theorem fixed_storage : Targets.MultivariateCollectedStorageInjective := storage
theorem fixed_additive : Targets.MultivariateCollectedAdditiveSemantics := additive

end LogicLineages.OrdinalComparison.MultivariateCollected.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariateCollected
