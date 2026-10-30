module
public import LogicLineages.OrdinalComparison.RawComparisonProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawComparisonCorrect : Targets.RawComparisonCorrect := rawComparisonCorrect

theorem fixed_rawComparisonPrimitiveRecursive : Targets.RawComparisonPrimitiveRecursive :=
  rawComparisonPrimitiveRecursive

theorem fixed_rawComparisonOrdinalCorrect : Targets.RawComparisonOrdinalCorrect :=
  rawComparisonOrdinalCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
