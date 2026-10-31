module
public import LogicLineages.OrdinalComparison.WWOriginalWeakReplacementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalWeakReplacement : Source.Targets.OriginalWeakReplacement :=
  Source.OriginalDomain.originalWeakReplacement

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
