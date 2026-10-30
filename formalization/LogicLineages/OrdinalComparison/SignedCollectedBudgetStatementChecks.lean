module

public import LogicLineages.OrdinalComparison.SignedCollectedBudgetProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_signedCollectedCoefficientBudget : LogicLineages.OrdinalComparison.Targets.SignedCollectedCoefficientBudget :=
  LogicLineages.OrdinalComparison.signedCollectedCoefficientBudget

theorem fixed_signedCollectedPairBudget : LogicLineages.OrdinalComparison.Targets.SignedCollectedPairBudget :=
  LogicLineages.OrdinalComparison.signedCollectedPairBudget

theorem fixed_signedCollectedRowIdentity : LogicLineages.OrdinalComparison.Targets.SignedCollectedRowIdentity :=
  LogicLineages.OrdinalComparison.signedCollectedRowIdentity

theorem fixed_signedAffineTailNonzero : LogicLineages.OrdinalComparison.Targets.SignedAffineTailNonzero :=
  LogicLineages.OrdinalComparison.signedAffineTailNonzero

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
