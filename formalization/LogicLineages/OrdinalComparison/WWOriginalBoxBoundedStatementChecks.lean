module
public import LogicLineages.OrdinalComparison.WWOriginalBoxBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalBoxTailGradeAndNorm : Source.Targets.OriginalBoxTailGradeAndNorm :=
  Source.OriginalDomain.originalBoxTailGradeAndNorm

theorem fixed_originalSourceBoxBounded : Source.Targets.OriginalSourceBoxBounded :=
  Source.OriginalDomain.originalSourceBoxBounded

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
