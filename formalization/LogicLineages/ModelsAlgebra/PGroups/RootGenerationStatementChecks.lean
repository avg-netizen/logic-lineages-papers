module

public import LogicLineages.ModelsAlgebra.PGroups.RootGeneration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_ulm_roots_generate : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmRootsGenerate :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_roots_generate

theorem fixed_bounded_socle_detects_injectivity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedSocleDetectsInjectivity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_socle_detects_injectivity

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
