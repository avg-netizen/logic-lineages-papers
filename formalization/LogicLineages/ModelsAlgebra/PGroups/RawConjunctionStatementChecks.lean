module

public import LogicLineages.ModelsAlgebra.PGroups.RawConjunction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_countable_conjunction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawCountableConjunction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_countable_conjunction

theorem fixed_raw_pi_conjunction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawPiConjunction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_pi_conjunction

theorem fixed_raw_difference_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawDifferenceAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_difference_agreement

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
