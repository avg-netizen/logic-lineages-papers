module

public import LogicLineages.ModelsAlgebra.PGroups.UlmTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_injective_socle_map : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInjectiveSocleMap :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.injective_socle_map

theorem fixed_injective_ulm_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInjectiveUlmIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.injective_ulm_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
