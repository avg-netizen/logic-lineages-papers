module
public import LogicLineages.OrdinalComparison.SourceBooleanPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanPlan.StatementChecks
 theorem gatesExact : Targets.GatesExact := Proof.gatesExact
 theorem bindExact : Targets.BindExact := Proof.bindExact
 theorem matrixExact : Targets.MatrixExact := Proof.matrixExact
 theorem linearOverhead : Targets.LinearOverhead := Proof.linearOverhead
end LogicLineages.OrdinalComparison.Source.BooleanPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.BooleanPlan
