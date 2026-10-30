module

public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_encodedFiniteTailPrimitiveRecursive : LogicLineages.OrdinalComparison.Targets.EncodedFiniteTailPrimitiveRecursive :=
  LogicLineages.OrdinalComparison.encodedFiniteTailPrimitiveRecursive

theorem fixed_encodedFiniteTailCorrect : LogicLineages.OrdinalComparison.Targets.EncodedFiniteTailCorrect :=
  LogicLineages.OrdinalComparison.encodedFiniteTailCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
