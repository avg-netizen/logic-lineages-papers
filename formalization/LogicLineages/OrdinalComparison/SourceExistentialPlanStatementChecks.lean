module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.StatementChecks
theorem compilation : Targets.Compilation := Proof.compilation
theorem size : Targets.Size := Proof.size
theorem comparison : Targets.Comparison := Proof.comparison
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan
