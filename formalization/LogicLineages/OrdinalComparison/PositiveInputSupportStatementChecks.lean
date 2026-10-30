module

public import LogicLineages.OrdinalComparison.PositiveInputSupportProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_positiveClosedProgramCorrect : LogicLineages.OrdinalComparison.Targets.PositiveClosedProgramCorrect :=
  LogicLineages.OrdinalComparison.positiveClosedProgramCorrect

theorem fixed_positiveClosedProgramTotal : LogicLineages.OrdinalComparison.Targets.PositiveClosedProgramTotal :=
  LogicLineages.OrdinalComparison.positiveClosedProgramTotal

theorem fixed_positiveInputAbsent : LogicLineages.OrdinalComparison.Targets.PositiveInputAbsent :=
  LogicLineages.OrdinalComparison.positiveInputAbsent

theorem fixed_positiveInputPresentLower : LogicLineages.OrdinalComparison.Targets.PositiveInputPresentLower :=
  LogicLineages.OrdinalComparison.positiveInputPresentLower

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
