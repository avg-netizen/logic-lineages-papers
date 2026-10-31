module
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdmissiblePartialGenerated : Source.Targets.ActualAdmissiblePartialGenerated :=
  Source.AdmissiblePartial.actualAdmissiblePartialGenerated

theorem fixed_actualAdmissiblePartialValue : Source.Targets.ActualAdmissiblePartialValue :=
  Source.AdmissiblePartial.actualAdmissiblePartialValue

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.AdmissiblePartial
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
