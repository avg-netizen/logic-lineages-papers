module

public import LogicLineages.ModelsAlgebra.PGroups.BackForth
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.BackForthStatementChecks

theorem fixed_groupTermProductEvaluation : Targets.groupTermProductEvaluation :=
  GroupBackAndForth.term_product_evaluation
theorem fixed_groupBackForthZero : Targets.groupBackForthZero := GroupBackAndForth.zero_comparison
theorem fixed_groupBackForthPositive : Targets.groupBackForthPositive :=
  GroupBackAndForth.positive_comparison
theorem fixed_groupFiniteProductPreservation : Targets.groupFiniteProductPreservation :=
  GroupBackAndForth.finite_product_preservation

end LogicLineages.ModelsAlgebra.PGroups.BackForthStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
