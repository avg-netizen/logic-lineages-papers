module

public import LogicLineages.ModelsAlgebra.Forests.CombForestProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem combFamilyBinary : LogicLineages.ModelsAlgebra.Forests.Targets.CombFamilyBinary :=
  LogicLineages.ModelsAlgebra.Forests.CombForestProof.combFamilyBinary

theorem combNontrivialClustersNested : LogicLineages.ModelsAlgebra.Forests.Targets.CombNontrivialClustersNested :=
  LogicLineages.ModelsAlgebra.Forests.CombForestProof.combNontrivialClustersNested

theorem actualCombForest : LogicLineages.ModelsAlgebra.Forests.Targets.ActualCombForest :=
  LogicLineages.ModelsAlgebra.Forests.CombForestProof.actualCombForest

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
