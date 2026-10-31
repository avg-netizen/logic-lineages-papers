module
public import LogicLineages.OrdinalComparison.WWOriginalBoxControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalBoxNumericalStep : Source.Targets.OriginalBoxNumericalStep :=
  Source.OriginalDomain.originalBoxNumericalStep

theorem fixed_originalBoxControlEnvelope : Source.Targets.OriginalBoxControlEnvelope :=
  Source.OriginalDomain.originalBoxControlEnvelope

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
