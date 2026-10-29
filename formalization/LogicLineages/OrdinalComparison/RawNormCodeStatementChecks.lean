module

public import LogicLineages.OrdinalComparison.RawNormCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawNormTableEquation : Targets.RawNormTableEquation :=
  rawNormTableEquation

theorem fixed_rawNormCodeEquation : Targets.RawNormCodeEquation :=
  rawNormCodeEquation

theorem fixed_rawNormCodeCorrect : Targets.RawNormCodeCorrect :=
  rawNormCodeCorrect

theorem fixed_rawNormCodePrimitiveRecursive : Targets.RawNormCodePrimitiveRecursive :=
  rawNormCodePrimitiveRecursive

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
