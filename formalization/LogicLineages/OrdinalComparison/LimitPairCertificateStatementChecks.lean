module
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.LimitPairCertificate.StatementChecks

theorem fixed_principal_source : Targets.ComparisonPrincipalNoteSource := principal_source
theorem fixed_certificate_program : Targets.ActualLimitPairCertificateProgram := actual_program

end LogicLineages.OrdinalComparison.LimitPairCertificate.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.LimitPairCertificate
