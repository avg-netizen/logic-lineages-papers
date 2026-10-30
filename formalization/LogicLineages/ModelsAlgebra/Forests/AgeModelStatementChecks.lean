module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem orderModelEmbeddingCalibration : LogicLineages.ModelsAlgebra.Forests.Targets.OrderModelEmbeddingCalibration :=
  LogicLineages.ModelsAlgebra.Forests.AgeModelProof.orderModelEmbeddingCalibration

theorem orderModelIsoCalibration : LogicLineages.ModelsAlgebra.Forests.Targets.OrderModelIsoCalibration :=
  LogicLineages.ModelsAlgebra.Forests.AgeModelProof.orderModelIsoCalibration

theorem relationalFiniteForestPullback : LogicLineages.ModelsAlgebra.Forests.Targets.RelationalFiniteForestPullback :=
  LogicLineages.ModelsAlgebra.Forests.AgeModelProof.relationalFiniteForestPullback

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
