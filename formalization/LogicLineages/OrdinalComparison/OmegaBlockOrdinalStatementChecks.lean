module
public import LogicLineages.OrdinalComparison.OmegaBlockOrdinalProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOmegaOmegaFacts : Targets.ActualOmegaOmegaFacts := actualOmegaOmegaFacts
theorem fixed_actualOmegaOmegaMaximum : Targets.ActualOmegaOmegaMaximum := actualOmegaOmegaMaximum
theorem fixed_actualOmegaBlockFirstStep : Targets.ActualOmegaBlockFirstStep := actualOmegaBlockFirstStep

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
