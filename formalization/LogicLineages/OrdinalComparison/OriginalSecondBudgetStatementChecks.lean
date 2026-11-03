module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetTargets
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.StatementChecks
theorem exact_scalar_second : Targets.ExactScalarSecond := Proof.exactScalarSecond
theorem actual_source_second : Targets.ActualSourceSecond := Proof.actualSourceSecond
theorem original_full_box_budget : Targets.OriginalFullBoxBudget := Proof.originalFullBoxBudget
end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget
