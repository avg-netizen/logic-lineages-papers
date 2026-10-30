module
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawDivisiblePrefixNormAddition : Targets.RawDivisiblePrefixNormAddition :=
  rawDivisiblePrefixNormAddition
theorem fixed_actualDivisiblePrefixNormAddition : Targets.ActualDivisiblePrefixNormAddition :=
  actualDivisiblePrefixNormAddition

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
