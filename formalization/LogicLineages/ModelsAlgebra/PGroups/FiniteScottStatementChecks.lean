module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.FiniteScottStatementChecks

theorem fixed_one_image_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupOneImageIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.one_image_isomorphism

theorem fixed_finite_isomorphism_sentence : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteIsomorphismSentence :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_isomorphism_sentence

theorem fixed_finite_difference_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteDifferenceScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_difference_scott

end LogicLineages.ModelsAlgebra.PGroups.FiniteScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
