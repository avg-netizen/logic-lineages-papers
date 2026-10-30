module
public import LogicLineages.OrdinalComparison.ControlledStepProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualControlledStepStrict : Targets.ActualControlledStepStrict := actualControlledStepStrict
theorem fixed_actualControlledStepNorm : Targets.ActualControlledStepNorm := actualControlledStepNorm
theorem fixed_actualControlledStepsJointMonotone : Targets.ActualControlledStepsJointMonotone :=
  actualControlledStepsJointMonotone

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
