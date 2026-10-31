module
public import LogicLineages.OrdinalComparison.WWAdmissibleExpansionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdmissiblePartialExpansion : Source.Targets.ActualAdmissiblePartialExpansion :=
  Source.AdmissibleExpansion.actualAdmissiblePartialExpansion

theorem fixed_actualAdmissibleRepeatExpansion : Source.Targets.ActualAdmissibleRepeatExpansion :=
  Source.AdmissibleExpansion.actualAdmissibleRepeatExpansion

theorem fixed_actualLiteralBoxExpansion : Source.Targets.ActualLiteralBoxExpansion :=
  Source.AdmissibleExpansion.actualLiteralBoxExpansion

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
