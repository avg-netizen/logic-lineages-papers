module

public import LogicLineages.ModelsAlgebra.Forests.WidthTargets
public import LogicLineages.ModelsAlgebra.Forests.WidthFacts
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.WidthStatementChecks

theorem everyVertexBelowLeaf : Targets.everyVertexBelowLeaf := by
  intro α _ _ x
  exact exists_leaf_above x

theorem widthBoundIffLeafBound : Targets.widthBoundIffLeafBound := by
  intro α _ _ hForest m
  exact widthAtMost_iff_leaf_card hForest m

end LogicLineages.ModelsAlgebra.Forests.WidthStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
