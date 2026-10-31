module
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdmissibleSumSyntax : Source.Targets.ActualAdmissibleSumSyntax :=
  Source.AdmissibleSum.actualAdmissibleSumSyntax

theorem fixed_actualAdmissibleSumValue : Source.Targets.ActualAdmissibleSumValue :=
  Source.AdmissibleSum.actualAdmissibleSumValue

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.AdmissibleSum
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
