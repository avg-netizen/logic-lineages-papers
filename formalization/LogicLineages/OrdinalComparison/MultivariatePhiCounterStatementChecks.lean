module
public import LogicLineages.OrdinalComparison.MultivariatePhiCounterProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariatePhiCounter.StatementChecks

theorem fixed_source : Targets.MultivariateWeightedRaySource := source
theorem fixed_code : Targets.MultivariateCounterRayCode := code
theorem fixed_phi_counter : Targets.MultivariatePhiRayCounter := phi_counter

end LogicLineages.OrdinalComparison.MultivariatePhiCounter.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.MultivariatePhiCounter
