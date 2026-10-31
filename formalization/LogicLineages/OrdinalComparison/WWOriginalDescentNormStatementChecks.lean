module
public import LogicLineages.OrdinalComparison.WWOriginalDescentNormProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalAddChildNorm : Source.Targets.OriginalAddChildNorm :=
  Source.OriginalDomain.originalAddChildNorm

theorem fixed_originalExpChildNorm : Source.Targets.OriginalExpChildNorm :=
  Source.OriginalDomain.originalExpChildNorm

theorem fixed_originalCollapseChildNorm : Source.Targets.OriginalCollapseChildNorm :=
  Source.OriginalDomain.originalCollapseChildNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
