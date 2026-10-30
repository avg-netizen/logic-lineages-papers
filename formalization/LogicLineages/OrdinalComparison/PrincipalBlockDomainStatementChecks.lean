module

public import LogicLineages.OrdinalComparison.PrincipalBlockDomainProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPrincipalBlockSumDomain : LogicLineages.OrdinalComparison.Targets.ActualPrincipalBlockSumDomain :=
  LogicLineages.OrdinalComparison.actualPrincipalBlockSumDomain

theorem fixed_actualPrincipalBlockUpperBound : LogicLineages.OrdinalComparison.Targets.ActualPrincipalBlockUpperBound :=
  LogicLineages.OrdinalComparison.actualPrincipalBlockUpperBound

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
