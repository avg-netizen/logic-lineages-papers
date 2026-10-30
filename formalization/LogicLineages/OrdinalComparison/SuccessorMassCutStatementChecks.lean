module

public import LogicLineages.OrdinalComparison.SuccessorMassCutProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSuccessorMassResidualCuts : LogicLineages.OrdinalComparison.Targets.ActualSuccessorMassResidualCuts :=
  LogicLineages.OrdinalComparison.actualSuccessorMassResidualCuts

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
