module

public import LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem laminarLeafEquivRelabeling : LogicLineages.ModelsAlgebra.Forests.Targets.LaminarLeafEquivRelabeling :=
  LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof.laminarLeafEquivRelabeling

theorem smallForestLeafLabeling : LogicLineages.ModelsAlgebra.Forests.Targets.SmallForestLeafLabeling :=
  LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof.smallForestLeafLabeling

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
