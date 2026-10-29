module

public import LogicLineages.ModelsAlgebra.Differential.RationalTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem algebraicConstantsOfIntegerDerivation :
    Targets.algebraicConstantsOfIntegerDerivation := by
  intro F _ _ D x hx
  exact integerDerivation_eq_zero_of_isAlgebraic D hx

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
