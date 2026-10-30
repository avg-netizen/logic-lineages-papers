module

public import LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem actualForestModelAgeCalibration : LogicLineages.ModelsAlgebra.Forests.Targets.ActualForestModelAgeCalibration :=
  LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof.actualForestModelAgeCalibration

theorem fullForestAgeRealization : LogicLineages.ModelsAlgebra.Forests.Targets.FullForestAgeRealization :=
  LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof.fullForestAgeRealization

theorem unboundedForestAgeRealization : LogicLineages.ModelsAlgebra.Forests.Targets.UnboundedForestAgeRealization :=
  LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof.unboundedForestAgeRealization

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
