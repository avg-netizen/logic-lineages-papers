module

public import LogicLineages.OrdinalComparison.EncodedKernelWordProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_encodedKernelWordComputable : LogicLineages.OrdinalComparison.Targets.EncodedKernelWordComputable :=
  LogicLineages.OrdinalComparison.encodedKernelWordComputable

theorem fixed_encodedKernelWordCorrect : LogicLineages.OrdinalComparison.Targets.EncodedKernelWordCorrect :=
  LogicLineages.OrdinalComparison.encodedKernelWordCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
