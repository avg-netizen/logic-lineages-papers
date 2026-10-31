module
public import LogicLineages.OrdinalComparison.SourceGroundArithmeticCounterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.StatementChecks
 theorem pointwise : Targets.Pointwise := Proof.pointwise
 theorem unsatisfiable : Targets.Unsatisfiable := Proof.unsatisfiable
 theorem groundQuery : Targets.GroundQuery := Proof.groundQuery
end LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter
