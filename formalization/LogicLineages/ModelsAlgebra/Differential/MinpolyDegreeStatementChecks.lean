module

public import LogicLineages.ModelsAlgebra.Differential.Targets
public import LogicLineages.ModelsAlgebra.Differential.ConstantsMinpolyDegree
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.MinpolyDegree.StatementChecks

theorem algebraicConstants : Targets.algebraicConstants := by
  intro F _ _ D x hx
  exact derivation_eq_zero_of_isAlgebraic D hx

theorem nonconstantTranscendental : Targets.nonconstantTranscendental := by
  intro F _ _ D x hx
  exact transcendental_of_derivation_ne_zero D hx

end LogicLineages.ModelsAlgebra.Differential.MinpolyDegree.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential.MinpolyDegree
