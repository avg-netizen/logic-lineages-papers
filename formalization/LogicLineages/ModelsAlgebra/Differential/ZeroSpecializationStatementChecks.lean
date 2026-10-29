module

public import LogicLineages.ModelsAlgebra.Differential.ZeroSpecialization
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_zeroSpecializationTwoConstants : Targets.zeroSpecializationTwoConstants :=
  ZeroSpecialization.zeroSpecializationTwoConstants

theorem fixed_distinctRationalRootsNotIsomorphic : Targets.distinctRationalRootsNotIsomorphic :=
  ZeroSpecialization.distinctRationalRootsNotIsomorphic

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
