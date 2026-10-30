module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem binaryClusterRelabeling : LogicLineages.ModelsAlgebra.Forests.Targets.BinaryClusterRelabeling :=
  LogicLineages.ModelsAlgebra.Forests.LaminarForestProof.binaryClusterRelabeling

theorem laminarFamilyForestRepresentation : LogicLineages.ModelsAlgebra.Forests.Targets.LaminarFamilyForestRepresentation :=
  LogicLineages.ModelsAlgebra.Forests.LaminarForestProof.laminarFamilyForestRepresentation

theorem binaryFamilyForestRepresentation : LogicLineages.ModelsAlgebra.Forests.Targets.BinaryFamilyForestRepresentation :=
  LogicLineages.ModelsAlgebra.Forests.LaminarForestProof.binaryFamilyForestRepresentation

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
