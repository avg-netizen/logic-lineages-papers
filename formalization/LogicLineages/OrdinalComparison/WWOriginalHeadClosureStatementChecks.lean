module
public import LogicLineages.OrdinalComparison.WWOriginalHeadClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalHeadClosureValue : Source.Targets.OriginalHeadClosureValue :=
  Source.OriginalDomain.originalHeadClosureValue

theorem fixed_originalHeadClosureNormPremise : Source.Targets.OriginalHeadClosureNormPremise :=
  Source.OriginalDomain.originalHeadClosureNormPremise

theorem fixed_originalHeadClosureGrade : Source.Targets.OriginalHeadClosureGrade :=
  Source.OriginalDomain.originalHeadClosureGrade

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
