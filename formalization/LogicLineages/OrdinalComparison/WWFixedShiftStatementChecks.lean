module
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_closedPositiveValuePositive : Source.Targets.ClosedPositiveValuePositive :=
  Source.ForwardTranslation.closedPositiveValuePositive

theorem fixed_scalarFixedHeadAdmissible : Source.Targets.ScalarFixedHeadAdmissible :=
  Source.ForwardTranslation.scalarFixedHeadAdmissible

theorem fixed_scalarFixedShiftComputable : Source.Targets.ScalarFixedShiftComputable :=
  Source.ForwardTranslation.scalarFixedShiftComputable

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
