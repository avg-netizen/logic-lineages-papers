module

public import LogicLineages.OrdinalComparison.SignedCollectedOrientationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_signedCollectedPeakOrientation : LogicLineages.OrdinalComparison.Targets.SignedCollectedPeakOrientation :=
  LogicLineages.OrdinalComparison.signedCollectedPeakOrientation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
