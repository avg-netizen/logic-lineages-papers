module

public import LogicLineages.OrdinalComparison.LinkedResidueLaurentProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLinkedResidueFormula : LogicLineages.OrdinalComparison.Targets.ActualLinkedResidueFormula :=
  LogicLineages.OrdinalComparison.actualLinkedResidueFormula

theorem fixed_fullActualSourceResidue : LogicLineages.OrdinalComparison.Targets.FullActualSourceResidue :=
  LogicLineages.OrdinalComparison.fullActualSourceResidue

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
