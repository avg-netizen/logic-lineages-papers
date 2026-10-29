module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteFiltration
public import LogicLineages.ModelsAlgebra.PGroups.ImageIntersections
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem subgroupImageCommutesWithPStep : Targets.subgroupImageCommutesWithPStep := by
  intro G H _ _ p f S
  exact map_pStep p f S

theorem finiteFiltrationImage : Targets.finiteFiltrationImage := by
  intro G H _ _ p f hf n
  exact map_finiteFiltration p f hf n

theorem saturatedIntersectionImage : Targets.saturatedIntersectionImage := by
  intro G H ι _ _ f hf S hker
  exact map_iInf_of_ker_le f hf S hker

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
