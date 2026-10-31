module
public import LogicLineages.OrdinalComparison.WWPolicyValueProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPolicyFixedInputValue : Source.Targets.ActualPolicyFixedInputValue :=
  Source.LiteralPolicy.actualPolicyFixedInputValue

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
