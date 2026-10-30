module

public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem adjacentClosedNeighborhoodsNested : Targets.AdjacentClosedNeighborhoodsNested :=
  GraphUniversalProof.adjacentClosedNeighborhoodsNested

theorem connectedForbiddenHasUniversalVertex : Targets.ConnectedForbiddenHasUniversalVertex :=
  GraphUniversalProof.connectedForbiddenHasUniversalVertex

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
