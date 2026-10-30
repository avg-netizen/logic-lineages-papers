module

public import LogicLineages.ModelsAlgebra.Forests.SplitForestProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem splitFamilyLaminar : LogicLineages.ModelsAlgebra.Forests.Targets.SplitFamilyLaminar :=
  LogicLineages.ModelsAlgebra.Forests.SplitForestProof.splitFamilyLaminar

theorem actualSplitForest : LogicLineages.ModelsAlgebra.Forests.Targets.ActualSplitForest :=
  LogicLineages.ModelsAlgebra.Forests.SplitForestProof.actualSplitForest

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
