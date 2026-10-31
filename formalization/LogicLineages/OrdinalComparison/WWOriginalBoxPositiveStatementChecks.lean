module
public import LogicLineages.OrdinalComparison.WWOriginalBoxPositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalBoxPositiveGrade : Source.Targets.OriginalBoxPositiveGrade :=
  Source.OriginalDomain.originalBoxPositiveGrade

theorem fixed_originalBoxPositiveNorm : Source.Targets.OriginalBoxPositiveNorm :=
  Source.OriginalDomain.originalBoxPositiveNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
