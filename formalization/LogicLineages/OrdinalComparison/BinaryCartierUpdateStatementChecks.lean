module

public import LogicLineages.OrdinalComparison.BinaryCartierUpdateProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualBinaryRationalCartierUpdate : LogicLineages.OrdinalComparison.Targets.ActualBinaryRationalCartierUpdate :=
  LogicLineages.OrdinalComparison.actualBinaryRationalCartierUpdate

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
