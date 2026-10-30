module

public import LogicLineages.ModelsAlgebra.PGroups.ElementaryScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.ElementaryScottStatementChecks

theorem fixed_elementary_abelian_sentence : LogicLineages.ModelsAlgebra.PGroups.Targets.groupElementaryAbelianSentence :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.elementary_abelian_sentence

theorem fixed_elementary_abelian_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupElementaryAbelianScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.elementary_abelian_scott

end LogicLineages.ModelsAlgebra.PGroups.ElementaryScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
