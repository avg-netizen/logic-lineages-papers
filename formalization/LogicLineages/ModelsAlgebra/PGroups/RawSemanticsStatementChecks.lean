module

public import LogicLineages.ModelsAlgebra.PGroups.RawSemantics
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_term_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawTermAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_term_agreement

theorem fixed_raw_qf_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawQFAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_qf_agreement

theorem fixed_raw_formula_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawFormulaAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_formula_agreement

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
