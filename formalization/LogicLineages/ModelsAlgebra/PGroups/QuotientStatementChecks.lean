module

public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.QuotientStatementChecks

theorem quotientFiltrationBelowCut : Targets.quotientFiltrationBelowCut := by
  intro G _ p T δ hT α hα
  exact quotient_filtration_below p T δ hT α hα

end LogicLineages.ModelsAlgebra.PGroups.QuotientStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
