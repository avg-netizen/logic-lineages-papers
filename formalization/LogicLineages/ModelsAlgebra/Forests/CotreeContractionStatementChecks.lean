module

public import LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem contractionCotreeValid : LogicLineages.ModelsAlgebra.Forests.Targets.ContractionCotreeValid :=
  LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof.contractionCotreeValid

theorem contractionCotreeGraphExact : LogicLineages.ModelsAlgebra.Forests.Targets.ContractionCotreeGraphExact :=
  LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof.contractionCotreeGraphExact

theorem concreteParentLabelContraction : LogicLineages.ModelsAlgebra.Forests.Targets.ConcreteParentLabelContraction :=
  LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof.concreteParentLabelContraction

theorem contractionGraphNonembedding : LogicLineages.ModelsAlgebra.Forests.Targets.ContractionGraphNonembedding :=
  LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof.contractionGraphNonembedding

theorem literalContractionTransferCounterexample : LogicLineages.ModelsAlgebra.Forests.Targets.LiteralContractionTransferCounterexample :=
  LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof.literalContractionTransferCounterexample

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
