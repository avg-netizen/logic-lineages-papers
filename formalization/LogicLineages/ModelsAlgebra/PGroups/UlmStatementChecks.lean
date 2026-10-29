module

public import LogicLineages.ModelsAlgebra.PGroups.UlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmIsomorphism
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.UlmStatementChecks

theorem localUlmMapBijective : Targets.localUlmMapBijective := by
  intro G H _ _ p S f hdeep
  exact UlmLocal.ulmMap_bijective p S f hdeep

end LogicLineages.ModelsAlgebra.PGroups.UlmStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
