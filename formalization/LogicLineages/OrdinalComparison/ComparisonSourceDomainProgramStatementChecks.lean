module
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain.StatementChecks

theorem fixed_primitive : Targets.ComparisonSourceDomainPrimitiveRecursive := primitive
theorem fixed_correct : Targets.ComparisonSourceDomainCorrect := correct

end LogicLineages.OrdinalComparison.ComparisonSourceDomain.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain
