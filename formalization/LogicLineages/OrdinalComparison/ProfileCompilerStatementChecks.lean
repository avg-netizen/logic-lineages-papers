module

public import LogicLineages.OrdinalComparison.ProfileCompilerProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualFixedLimitProfileMonotone : LogicLineages.OrdinalComparison.Targets.ActualFixedLimitProfileMonotone :=
  LogicLineages.OrdinalComparison.actualFixedLimitProfileMonotone

theorem fixed_actualProfileBoundCompiler : LogicLineages.OrdinalComparison.Targets.ActualProfileBoundCompiler :=
  LogicLineages.OrdinalComparison.actualProfileBoundCompiler

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
