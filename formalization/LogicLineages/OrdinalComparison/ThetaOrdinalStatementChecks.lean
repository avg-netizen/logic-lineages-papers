module
public import LogicLineages.OrdinalComparison.ThetaOrdinalProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOmegaMultipleFacts : Targets.ActualOmegaMultipleFacts := actualOmegaMultipleFacts
theorem fixed_actualThetaFacts : Targets.ActualThetaFacts := actualThetaFacts
theorem fixed_actualThetaBudgetMaximum : Targets.ActualThetaBudgetMaximum := actualThetaBudgetMaximum

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
