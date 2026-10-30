module

public import LogicLineages.OrdinalComparison.PrimitiveRootComplementProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPrimitiveRootComplement : LogicLineages.OrdinalComparison.Targets.ActualPrimitiveRootComplement :=
  LogicLineages.OrdinalComparison.actualPrimitiveRootComplement

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
