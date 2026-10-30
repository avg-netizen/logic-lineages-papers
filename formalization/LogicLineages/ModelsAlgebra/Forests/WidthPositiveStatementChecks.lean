module

public import LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem smallWidthTemplateCalibration : LogicLineages.ModelsAlgebra.Forests.Targets.SmallWidthTemplateCalibration :=
  LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof.smallWidthTemplateCalibration

theorem widthZeroHasJEP : LogicLineages.ModelsAlgebra.Forests.Targets.WidthZeroHasJEP :=
  LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof.widthZeroHasJEP

theorem widthAtMostThreeHasJEP : LogicLineages.ModelsAlgebra.Forests.Targets.WidthAtMostThreeHasJEP :=
  LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof.widthAtMostThreeHasJEP

theorem fullWidthJEPClassification : LogicLineages.ModelsAlgebra.Forests.Targets.FullWidthJEPClassification :=
  LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof.fullWidthJEPClassification

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
