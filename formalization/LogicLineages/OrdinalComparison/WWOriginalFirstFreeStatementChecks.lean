module
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalFirstFreeEndpoint : Source.Targets.OriginalFirstFreeEndpoint :=
  Source.OriginalDomain.originalFirstFreeEndpoint

theorem fixed_originalFirstFreeGrade : Source.Targets.OriginalFirstFreeGrade :=
  Source.OriginalDomain.originalFirstFreeGrade

theorem fixed_originalFirstFreeBound : Source.Targets.OriginalFirstFreeBound :=
  Source.OriginalDomain.originalFirstFreeBound

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
