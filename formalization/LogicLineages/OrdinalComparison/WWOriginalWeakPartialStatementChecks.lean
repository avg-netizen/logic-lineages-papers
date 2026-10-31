module
public import LogicLineages.OrdinalComparison.WWOriginalWeakPartialProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalPartialWeakAndValid : Source.Targets.OriginalPartialWeakAndValid :=
  Source.OriginalDomain.originalPartialWeakAndValid

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
