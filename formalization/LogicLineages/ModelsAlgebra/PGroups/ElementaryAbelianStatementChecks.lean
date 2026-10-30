module

public import LogicLineages.ModelsAlgebra.PGroups.ElementaryAbelian
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.ElementaryAbelianStatementChecks

theorem fixed_elementary_abelian_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupElementaryAbelianRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.elementary_abelian_rank

theorem fixed_elementary_abelian_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupElementaryAbelianIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.elementary_abelian_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.ElementaryAbelianStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
