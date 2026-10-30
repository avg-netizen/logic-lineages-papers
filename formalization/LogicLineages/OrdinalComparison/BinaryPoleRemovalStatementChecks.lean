module

public import LogicLineages.OrdinalComparison.BinaryPoleRemovalProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualBinaryHigherPoleRemoval : LogicLineages.OrdinalComparison.Targets.FullActualBinaryHigherPoleRemoval :=
  LogicLineages.OrdinalComparison.fullActualBinaryHigherPoleRemoval

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
