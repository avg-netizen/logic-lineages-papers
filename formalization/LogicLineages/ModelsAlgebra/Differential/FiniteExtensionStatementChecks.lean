module

public import LogicLineages.ModelsAlgebra.Differential.FiniteExtensionTargets
public import LogicLineages.ModelsAlgebra.Differential.FiniteExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem finiteDerivationExtension : Targets.finiteDerivationExtension := by
  intro F K _ _ _ _ _ D
  exact existsUnique_finite_derivation_extension D

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
