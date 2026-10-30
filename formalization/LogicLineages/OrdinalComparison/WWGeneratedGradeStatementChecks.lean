module

public import LogicLineages.OrdinalComparison.WWGeneratedGradeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualGeneratedGradeRenaming : LogicLineages.OrdinalComparison.Source.Targets.ActualGeneratedGradeRenaming :=
  LogicLineages.OrdinalComparison.Source.actualGeneratedGradeRenaming

theorem fixed_actualGeneratedGradeHeadClosure : LogicLineages.OrdinalComparison.Source.Targets.ActualGeneratedGradeHeadClosure :=
  LogicLineages.OrdinalComparison.Source.actualGeneratedGradeHeadClosure

theorem fixed_actualGeneratedGradePartial : LogicLineages.OrdinalComparison.Source.Targets.ActualGeneratedGradePartial :=
  LogicLineages.OrdinalComparison.Source.actualGeneratedGradePartial

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
