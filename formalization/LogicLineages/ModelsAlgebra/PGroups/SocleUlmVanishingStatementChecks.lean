module

public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishingStatementChecks

theorem fixed_ulm_rank_zero_socle : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmRankZeroSocle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_rank_zero_socle

theorem fixed_socle_root_ulm_vanishing : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleRootUlmVanishing :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.socle_root_ulm_vanishing

theorem fixed_socle_root_vanishing_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleRootVanishingFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.socle_root_vanishing_formula

end LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishingStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
