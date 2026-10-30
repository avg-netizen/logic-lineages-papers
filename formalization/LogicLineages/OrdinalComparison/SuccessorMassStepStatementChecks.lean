module

public import LogicLineages.OrdinalComparison.SuccessorMassStepProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSuccessorKernelStrictMassStep : LogicLineages.OrdinalComparison.Targets.ActualSuccessorKernelStrictMassStep :=
  LogicLineages.OrdinalComparison.actualSuccessorKernelStrictMassStep

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
