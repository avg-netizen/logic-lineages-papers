module

public import LogicLineages.OrdinalComparison.PositiveExprCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_positiveExprCodeRoundTrip : LogicLineages.OrdinalComparison.Targets.PositiveExprCodeRoundTrip :=
  LogicLineages.OrdinalComparison.positiveExprCodeRoundTrip

theorem fixed_positiveExprCodeInverse : LogicLineages.OrdinalComparison.Targets.PositiveExprCodeInverse :=
  LogicLineages.OrdinalComparison.positiveExprCodeInverse

theorem fixed_positiveExprCodeDomain : LogicLineages.OrdinalComparison.Targets.PositiveExprCodeDomain :=
  LogicLineages.OrdinalComparison.positiveExprCodeDomain

theorem fixed_positiveExprMalformedRejected : LogicLineages.OrdinalComparison.Targets.PositiveExprMalformedRejected :=
  LogicLineages.OrdinalComparison.positiveExprMalformedRejected

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
