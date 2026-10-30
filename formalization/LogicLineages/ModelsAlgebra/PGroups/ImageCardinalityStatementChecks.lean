module

public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinality
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityStatementChecks

theorem fixed_image_distinct_cardinality : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageDistinctCardinality :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_distinct_cardinality

theorem fixed_image_bound_cardinality : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageBoundCardinality :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_bound_cardinality

theorem fixed_bounded_multiple_image_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedMultipleImageFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_multiple_image_formula

theorem fixed_exact_multiple_image_card_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupExactMultipleImageCardFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.exact_multiple_image_card_formula

end LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
