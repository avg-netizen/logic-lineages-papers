module

public import LogicLineages.ModelsAlgebra.Forests.WidthAgeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem widthClassHereditary : LogicLineages.ModelsAlgebra.Forests.Targets.WidthClassHereditary :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.widthClassHereditary

theorem widthClassNonempty : LogicLineages.ModelsAlgebra.Forests.Targets.WidthClassNonempty :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.widthClassNonempty

theorem widthClassUnbounded : LogicLineages.ModelsAlgebra.Forests.Targets.WidthClassUnbounded :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.widthClassUnbounded

theorem realizedWidthAgeWidth : LogicLineages.ModelsAlgebra.Forests.Targets.RealizedWidthAgeWidth :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.realizedWidthAgeWidth

theorem widthAgeClassification : LogicLineages.ModelsAlgebra.Forests.Targets.WidthAgeClassification :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.widthAgeClassification

theorem smallWidthCountablyInfiniteAge : LogicLineages.ModelsAlgebra.Forests.Targets.SmallWidthCountablyInfiniteAge :=
  LogicLineages.ModelsAlgebra.Forests.WidthAgeProof.smallWidthCountablyInfiniteAge

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
