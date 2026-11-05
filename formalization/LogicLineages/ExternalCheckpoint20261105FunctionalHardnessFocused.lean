module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionStatementChecks
public meta import LogicLineages.Audit
@[expose] public section

/-! Exact coordinator interface for the complete reviewed functional-hardness theorem.
The fourteen original supplier gates are checked separately under the same limits.
This focused interface is not a full-project or prior-checkpoint aggregate build. -/
namespace LogicLineages.ExternalCheckpoint20261105FunctionalHardness

theorem full_functional_hardness :
    LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessTargets.FullFunctionalHardness :=
  LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.StatementChecks.full_functional_hardness

end LogicLineages.ExternalCheckpoint20261105FunctionalHardness
#audit_namespace LogicLineages.ExternalCheckpoint20261105FunctionalHardness
