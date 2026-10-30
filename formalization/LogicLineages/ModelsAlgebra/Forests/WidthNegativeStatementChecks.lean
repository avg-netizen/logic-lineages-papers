module

public import LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem clusterCommonHostObstruction : LogicLineages.ModelsAlgebra.Forests.Targets.ClusterCommonHostObstruction :=
  LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof.clusterCommonHostObstruction

theorem widthAtLeastFourFailsJEP : LogicLineages.ModelsAlgebra.Forests.Targets.WidthAtLeastFourFailsJEP :=
  LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof.widthAtLeastFourFailsJEP

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
