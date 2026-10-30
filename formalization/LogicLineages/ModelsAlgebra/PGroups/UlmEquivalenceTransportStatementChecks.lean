module

public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_isomorphism_finite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIsomorphismFiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.isomorphism_finite_filtration

theorem fixed_isomorphism_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIsomorphismUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.isomorphism_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
