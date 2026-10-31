module
public import LogicLineages.OrdinalComparison.WWOriginalBoxStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualNaturalProductUpperNorm : Source.Targets.ActualNaturalProductUpperNorm :=
  Source.OriginalDomain.actualNaturalProductUpperNorm

theorem fixed_originalBoxStepNorm : Source.Targets.OriginalBoxStepNorm :=
  Source.OriginalDomain.originalBoxStepNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
