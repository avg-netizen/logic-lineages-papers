module

public import LogicLineages.ModelsAlgebra.Differential.AlgebraicExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem algebraic_derivation_extension : Targets.algebraicDerivationExtension :=
  AlgebraicExtension.algebraicDerivationExtension

theorem algebraic_closure_derivation_extension : Targets.algebraicClosureDerivationExtension :=
  AlgebraicExtension.algebraicClosureDerivationExtension

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
