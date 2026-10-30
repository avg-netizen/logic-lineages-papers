module

public import LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem binaryClusterUniverseNonempty : LogicLineages.ModelsAlgebra.Forests.Targets.BinaryClusterUniverseNonempty :=
  LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof.binaryClusterUniverseNonempty

theorem binaryClusterFamilyMaximal : LogicLineages.ModelsAlgebra.Forests.Targets.BinaryClusterFamilyMaximal :=
  LogicLineages.ModelsAlgebra.Forests.BinaryClusterProof.binaryClusterFamilyMaximal

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
