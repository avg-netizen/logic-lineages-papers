module

public import LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem finitePatchesForestOrder : LogicLineages.ModelsAlgebra.Forests.Targets.FinitePatchesForestOrder :=
  LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof.finitePatchesForestOrder

theorem forestModelAgeFinitePatches : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelAgeFinitePatches :=
  LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof.forestModelAgeFinitePatches

theorem countableForestModelReconstruction : LogicLineages.ModelsAlgebra.Forests.Targets.CountableForestModelReconstruction :=
  LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof.countableForestModelReconstruction

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
