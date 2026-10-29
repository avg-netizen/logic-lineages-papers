module

public import LogicLineages.ModelsAlgebra.Differential.Targets
public import LogicLineages.ModelsAlgebra.Differential.Constants
public meta import LogicLineages.Audit

@[expose] public section

/-! Fixed statement gates. No hypothesis may be added to these signatures. -/

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem algebraicConstants : Targets.algebraicConstants := by
  intro F _ _ D x hx
  exact derivation_eq_zero_of_isAlgebraic D hx

theorem nonconstantTranscendental : Targets.nonconstantTranscendental := by
  intro F _ _ D x hx
  exact transcendental_of_derivation_ne_zero D hx

#print axioms algebraicConstants
#print axioms nonconstantTranscendental

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
