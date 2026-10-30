module

public import LogicLineages.OrdinalComparison.RealResidueBoundsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualRealExponentialRootGap : LogicLineages.OrdinalComparison.Targets.ActualRealExponentialRootGap :=
  LogicLineages.OrdinalComparison.actualRealExponentialRootGap

theorem fixed_fullActualLinkedResidueBounds : LogicLineages.OrdinalComparison.Targets.FullActualLinkedResidueBounds :=
  LogicLineages.OrdinalComparison.fullActualLinkedResidueBounds

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
