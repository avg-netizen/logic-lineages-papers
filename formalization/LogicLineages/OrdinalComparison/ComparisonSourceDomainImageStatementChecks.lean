module
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainImageProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain.StatementChecks

theorem fixed_image : Targets.ComparisonSourceDomainImage := image

end LogicLineages.OrdinalComparison.ComparisonSourceDomain.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain
