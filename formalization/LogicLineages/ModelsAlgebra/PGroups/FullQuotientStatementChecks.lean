module

public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.FullQuotientStatementChecks

theorem fullQuotientFiltrationLemma : Targets.fullQuotientFiltrationLemma := by
  intro G _ p _ T γ hT
  exact full_quotient_filtration p T γ hT

end LogicLineages.ModelsAlgebra.PGroups.FullQuotientStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
