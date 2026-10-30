module
public import LogicLineages.OrdinalComparison.CompatiblePrefixFactsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualMinExponentDivisibility : Targets.ActualMinExponentDivisibility :=
  actualMinExponentDivisibility
theorem fixed_compensatedPrefixControlBounds : Targets.CompensatedPrefixControlBounds :=
  compensatedPrefixControlBounds

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
