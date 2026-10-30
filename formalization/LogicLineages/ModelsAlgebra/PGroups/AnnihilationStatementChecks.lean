module

public import LogicLineages.ModelsAlgebra.PGroups.Annihilation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.AnnihilationStatementChecks

theorem fixed_annihilation_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAnnihilationFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.annihilation_formula

theorem fixed_finite_exponent_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteExponentFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_exponent_formula

end LogicLineages.ModelsAlgebra.PGroups.AnnihilationStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
