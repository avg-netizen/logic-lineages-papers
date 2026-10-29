module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.TransfiniteStatementChecks

theorem transfiniteFiltrationAntitone : Targets.transfiniteFiltrationAntitone := by
  intro G _ p
  exact transfiniteFiltration_antitone p

theorem transfiniteFiltrationImageBelowCut : Targets.transfiniteFiltrationImageBelowCut := by
  intro G H _ _ p f hf δ hker α hα
  exact map_transfiniteFiltration_below p f hf δ hker α hα

end LogicLineages.ModelsAlgebra.PGroups.TransfiniteStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
